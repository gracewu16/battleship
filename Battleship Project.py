#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Nov  8 00:37:23 2024

@author: Grace Wu
"""
# Project: Battleship
#  Design:
#     - GUI is based on Python tkinter
#     - use winsound (on Windows) to play game sound wave files
#     - use os.system(afplay) (on Mac, not tested) to play game sound wave files
#     - sound playing is run a separate thread so that UI thread is not blocked
#     - timer thread to keep updating game time
#     - Two views:
#       * Main View UI: three panels(Greeting, Player skill selection, Buttons for Play, Exit, Sound On/Off)
#       * Game View UI: three panels(Game Board, Game Information, Buttons for Quit and Sound On/Off)
#     - Show and keep tracking of missiles available, missiles missed, ships sunken
#     - Update game board (internal data, and graphic presentation) as game is being played
#     - Use mouse to select target grid on the board, the grid coordinate where missile is aiming at is displayed
#     - Animate missile launch, and show the last animate frame based on it's a miss or hit
#     - Sound wave is played with animation, based on the launch is a miss, hit or last ditch to sink a ship
#     - Record game start time and end time to calculate the duration of game
#     - Missile is launched by mouse click, invalid mouse click is ignored
#     - toggle game_cheat flag by press 'S' key before play game to place a red dot in grid to indicate ship
#       for development debug purpose

# Sources： 
# https://pythonbasics.org/tkinter/
# Ocean Image: https://www.istockphoto.com/photo/blue-open-sea-environment-travel-and-nature-concept-gm1147989465-309873354
# Missile GIF: https://gfycat.com/alienatedgoldenafricanaugurbuzzard
# Burning Ship GIF: https://www.rt.com/news/449357-kerch-strait-ships-fire/
# Radar Image: https://qph.fs.quoracdn.net/main-qimg-792c920d34b2940f52a925000e1f140b
# Green Grid Image: https://poki.com/en/g/battleship-war
# Sound Effect: https://www.freesoundeffects.com/free-sounds/explosion-10070/

from datetime import datetime  # use different seeds to generate different random patterns
from random import seed, randint   # for randomly place ships on board
import time      # for time function
import sys       # for sys argv platform
import os        # get sound play on mac
from os import getcwd   # get current working directory
from PIL import Image, ImageDraw, ImageFont, ImageTk    # image functions
import tkinter as ui       # graphic user interface
from tkinter import messagebox
import threading           # sound playing and UI should be on different threads
if sys.platform == 'win32':
    import winsound            # sound play on windows

sound_thread = None    # thread instance to play sound,
player_skill = None    # player's skill level

missiles_total = 50    # the max number of missiles at given skill level
hits_needed = 0        # the number of missile hits to sink all ships
ships_total = 0        # the number of ships
ships_sunken = 0       # the number of ships had been sunken

image_missiles = []   # list of images for firing missile animation
hit_jpg = None        # last animation image if ship is hit
missed_jpg = None     # last animation image if ship is not hit

# view is divided into upper, middle and lower panels
upper_fraction = 0.7
middle_fraction = 0.24
lower_fraction = 0.06
image_upper = None    # background image of upper panel
# panels in main view
upper_panel = None
middle_panel = None
lower_panel = None
sound_button = None # button handle for sound on/off

# panels of game view
game_upper_panel = None
game_middle_panel = None
game_lower_panel = None
game_sound_button = None  # button handle on game view to turn sound on/off
game_quit_button = None   # button handle on game view to quit game
game_image = None         # game image containing initial grid lines
game_photo = None         # game photo image based on game states
game_upper_label = None   # label to display game photo
game_coord_label = None   # label to display where the missile is pointing to
game_hits_label = None    # label to display the number of missile hits
game_miss_label = None    # label to display the number of missiles missed
game_missiles_label = None  # label to display the number of missiles still available
game_ships_live_label = None  # label to display the number of active ships
game_ships_sunken_label = None  # label to display the number of ship sunken
game_time_label = None        # label to display game time
game_start_time = 0    # game start time
game_missile_left = 0  # the number of missiles still available for game
game_hits = 0          # the number of missiles did hit ships
game_miss = 0          # the number of missiles did not ship
# missile aiming region limits
game_mouse_x_min = 0
game_mouse_x_max = 0
game_mouse_y_min = 0
game_mouse_y_max = 0

gaming = False     # flag indicates game is active
exiting = False    # flag indicates exiting program
timer_thread = None
mute_flag = False  # flag indicates mute sound

# grids
cols, rows = 10, 10
max_grids = cols * rows
# grid values for water
GRID_WATER_FREE = 0          # water, potential for ship placing
GRID_WATER_OBSTRUCTED = 1    # water but not for ship placing due to next to another ship
GRID_WATER_CLEARED = 3        # water either bombed by missile or cleared by sunken ship
# grid values for ship are greater than 9, (ship length)*GRID_SHIP_SCALE + GRID_SHIP_GOOD/BOMBED/BURNT
GRID_SHIP_GOOD = 2           # spot for ship, not hit by missile
GRID_SHIP_BOMBED = 4         # spot for ship, hit by missile
GRID_SHIP_BURNT = 8          # spot for ship, sunken
GRID_SHIP_SCALE = 10         # scale factor, ten's digit indicates the length of ship, one's digit is ship status

ship_locations = []   # initial ship layout on the board
game_data = []        # active game data (grid values of the board)

# board drawing parameters
left_margin, right_margin = 80, 80
grid_width, grid_height, upper_height = 0, 0, 0
line_width = 2
# image or photo handles
radar_photo = None
grid_ship_good_jpg = None
grid_ship_burning_jpg = None
grid_ship_burnt_jpg = None
grid_water_cleared_jpg = None
grid_water_obstructed_jpg = None

game_cheat = False


# check eight directions if given location (row, col) is good for ship placing
def good_location(value, r, c):
    row, col = int(r), int(c)
    if game_data[row][col] != GRID_WATER_FREE:   # must be free water
        return False
    if row > 0:   # check upper row
        if game_data[row-1][col] > GRID_WATER_OBSTRUCTED and game_data[row-1][col] != value:
            return False
        if col > 0 and game_data[row-1][col-1] > GRID_WATER_OBSTRUCTED and game_data[row-1][col-1] != value:
            return False
        if col < cols-1 and game_data[row-1][col+1] > GRID_WATER_OBSTRUCTED and game_data[row-1][col+1] != value:
            return False
    if col > 0 and game_data[row][col-1] > GRID_WATER_OBSTRUCTED and game_data[row][col-1] != value:
        return False   # check left
    if col < cols-1 and game_data[row][col+1] > GRID_WATER_OBSTRUCTED and game_data[row][col+1] != value:
        return False   # check right
    if row < rows-1:   # check lower row
        if game_data[row+1][col] > GRID_WATER_OBSTRUCTED and game_data[row+1][col] != value:
            return False
        if col > 0 and game_data[row+1][col-1] > GRID_WATER_OBSTRUCTED and game_data[row+1][col-1] != value:
            return False
        if col < cols-1 and game_data[row+1][col+1] > GRID_WATER_OBSTRUCTED and game_data[row+1][col+1] != value:
            return False
    return True


# when a grid is taken by ship, mark eight directions are no longer available for other ship placing
def obstruct_neighbour(r, c):
    row, col = int(r), int(c)
    global game_data
    if row > 0:  # upper row
        if game_data[row-1][col] == GRID_WATER_FREE:
            game_data[row-1][col] = GRID_WATER_OBSTRUCTED
        if col > 0 and game_data[row-1][col-1] == GRID_WATER_FREE:
            game_data[row-1][col-1] = GRID_WATER_OBSTRUCTED
        if col < cols - 1 and game_data[row-1][col + 1] == GRID_WATER_FREE:
            game_data[row-1][col + 1] = GRID_WATER_OBSTRUCTED
    if col > 0 and game_data[row][col-1] == GRID_WATER_FREE:
        game_data[row][col-1] = GRID_WATER_OBSTRUCTED   # left
    if col < cols-1 and game_data[row][col+1] == GRID_WATER_FREE:
        game_data[row][col+1] = GRID_WATER_OBSTRUCTED   # right
    if row < rows-1:  # lower row
        if game_data[row+1][col] == GRID_WATER_FREE:
            game_data[row+1][col] = GRID_WATER_OBSTRUCTED
        if col > 0 and game_data[row+1][col - 1] == GRID_WATER_FREE:
            game_data[row+1][col - 1] = GRID_WATER_OBSTRUCTED
        if col < cols - 1 and game_data[row+1][col + 1] == GRID_WATER_FREE:
            game_data[row+1][col + 1] = GRID_WATER_OBSTRUCTED


def water_cleared(r, c):    # each grid of sunken ship will clear its neighboring water grids
    row, col = int(r), int(c)
    global game_data
    if row > 0:   # upper row
        if game_data[row-1][col] < GRID_WATER_CLEARED:
            game_data[row-1][col] = GRID_WATER_CLEARED
        if col > 0 and game_data[row-1][col - 1] < GRID_WATER_CLEARED:
            game_data[row-1][col - 1] = GRID_WATER_CLEARED
        if col < cols - 1 and game_data[row-1][col + 1] < GRID_WATER_CLEARED:
            game_data[row-1][col + 1] = GRID_WATER_CLEARED
    if row < rows-1:  # lower row
        if game_data[row+1][col] < GRID_WATER_CLEARED:
            game_data[row+1][col] = GRID_WATER_CLEARED
        if col > 0 and game_data[row+1][col - 1] < GRID_WATER_CLEARED:
            game_data[row+1][col - 1] = GRID_WATER_CLEARED
        if col < cols - 1 and game_data[row+1][col + 1] < GRID_WATER_CLEARED:
            game_data[row+1][col + 1] = GRID_WATER_CLEARED
    if col > 0 and game_data[row][col-1] < GRID_WATER_CLEARED:
        game_data[row][col-1] = GRID_WATER_CLEARED  # left
    if col < cols-1 and game_data[row][col+1] < GRID_WATER_CLEARED:
        game_data[row][col+1] = GRID_WATER_CLEARED  # right


# place n ships of length into ship_locations
def place_ships(n, length):
    if n == 0:
        return
    value = GRID_SHIP_SCALE*length + GRID_SHIP_GOOD
    placed = False
    global game_data
    while not placed:    # loop until the ship is placed successfully
        location = randint(0, max_grids-1)
        col = int(location % cols)
        row = int(location / cols)
        if not good_location(value, row, col):   # current grid is not good to place ship
            continue
        if length == 1:     # ship takes one grid, done
            game_data[row][col] = value
            obstruct_neighbour(row, col)
            break
        direction = randint(0, 3)      # ship takes more than one grid, select a direction to probe
        if direction == 0 and col+length < cols:
            good = True
            for i in range(1, length):
                if not good_location(value, row, col+i):
                    good = False
                    break
            if not good:
                continue
            for i in range(length):     # have good grids needs by the ship, place whole ship
                game_data[row][col+i] = value
            for i in range(length):     # mark all neighboring grids not available to place other ship
                obstruct_neighbour(row, col + i)
                placed = True
        elif direction == 1 and col+1 >= length:
            good = True
            for i in range(1, length):
                if not good_location(value, row, col-i):
                    good = False
                    break
            if not good:
                continue
            for i in range(length):   # have good grids needs by the ship, place whole ship
                game_data[row][col-i] = value
            for i in range(length):
                obstruct_neighbour(row, col-i)
                placed = True
        elif direction == 2 and row+length < rows:
            good = True
            for i in range(1, length):
                if not good_location(value, row+i, col):
                    good = False
                    break
            if not good:
                continue
            for i in range(length):   # have good grids needs by the ship, place whole ship
                game_data[row+i][col] = value
            for i in range(length):   # mark all neighboring grids not available to place other ship
                obstruct_neighbour(row+i, col)
                placed = True
        elif direction == 3 and row+1 >= length:
            good = True
            for i in range(1, length):
                if not good_location(value, row-i, col):
                    good = False
                    break
            if not good:
                continue
            for i in range(length):  # have good grids needs by the ship, place whole ship
                game_data[row-i][col] = value
            for i in range(length):  # mark all neighboring grids not available to place other ship
                obstruct_neighbour(row-i, col)
                placed = True
    # recursive call to place the next ship
    place_ships(n-1, length)


def init_game():
    seed(datetime.now())
    global ship_locations, game_data, hits_needed, ships_total, ships_sunken
    game_data = [[GRID_WATER_FREE] * rows for _ in range(cols)]
    # place all ships
    place_ships(1, 4)   # one FOUR
    place_ships(2, 3)   # two THREE
    place_ships(3, 2)   # three TWO
    place_ships(4, 1)   # four ONE
    hits_needed = 1*4 + 2*3 + 3*2 + 4*1   # need this many missile hits to sink all ships
    ships_total = 1+2+3+4    # total ships placed on the board
    ships_sunken = 0         # no ships are sunken yet

    # copy ship layout to progress
    ship_locations = game_data.copy()   # keep a copy of board with ships placed

    global grid_width, grid_height, upper_height
    global game_mouse_x_min, game_mouse_x_max, game_mouse_y_min, game_mouse_y_max
    width, height = main_size[0], main_size[1]
    upper_height = round(height * upper_fraction)
    # compute grid width, height, mouse limits for missile targeting
    grid_width = (width - left_margin - right_margin - (cols+1)*line_width)/float(cols)
    grid_height = (upper_height - (rows+1)*line_width)/float(rows)
    game_mouse_x_min = left_margin
    game_mouse_x_max = width - right_margin
    game_mouse_y_min = 0
    game_mouse_y_max = upper_height - 1
    global grid_ship_burning_jpg, grid_ship_burnt_jpg, grid_water_cleared_jpg
    global grid_water_obstructed_jpg, grid_ship_good_jpg, radar_photo
    dx, dy = int(grid_width), int(grid_height)
    # load images and resize them
    grid_ship_good_jpg = None
    if game_cheat:
        grid_ship_good_jpg = Image.new("RGB", (2, 2), color='red')
    grid_ship_burning_jpg = Image.open(cur_directory+"/ship_burning.jpg")
    grid_ship_burning_jpg = grid_ship_burning_jpg.resize((dx, dy), Image.BILINEAR)
    grid_ship_burnt_jpg = Image.open(cur_directory+"/ship_burnt.jpg")
    grid_ship_burnt_jpg = grid_ship_burnt_jpg.resize((dx, dy), Image.BILINEAR)
    grid_water_cleared_jpg = Image.open(cur_directory+"/water_cleared.jpg")
    grid_water_cleared_jpg = grid_water_cleared_jpg.resize((dx, dy), Image.BILINEAR)
    grid_water_obstructed_jpg = None
    radar_image = Image.open(cur_directory+"/radar.jpg")
    radar_image = radar_image.resize((100, 100), Image.BILINEAR)
    radar_photo = ImageTk.PhotoImage(radar_image)


# option 0 - just grids, option 1 - ship locations, option 2 - game data
def draw_game(option):
    global game_image, game_photo
    game_image = image_ocean.copy()     # make a copy of the ocean image
    play_draw = ImageDraw.Draw(game_image)     # make the copy image as drawing canvas
    width, height = main_size[0], main_size[1]
    for i in range(cols+1):     # draw horizontal grid lines
        play_draw.line((left_margin + round(i*grid_width+i*line_width), 0, left_margin+round(i*grid_width+i*line_width),
                        upper_height-line_width), fill='green', width=line_width)
    for i in range(rows+1):     # draw vertical grid lines
        play_draw.line((left_margin, round(i*grid_height+i*line_width), width-right_margin-line_width,
                        round(i*grid_height+i*line_width)), fill='green', width=line_width)
    data = None
    if option == 1:
        data = ship_locations.copy()   # draw ship placing board
    elif option == 2:
        data = game_data.copy()    # draw current game board
    if data:
        for row in range(rows):
            for col in range(cols):
                offset = (left_margin+int(col*grid_width+(col+1)*line_width), int(row*grid_height+(row+1)*line_width))
                switcher = {
                    GRID_WATER_FREE: None,
                    GRID_WATER_OBSTRUCTED: grid_water_obstructed_jpg,
                    GRID_SHIP_GOOD: grid_ship_good_jpg,
                    GRID_WATER_CLEARED: grid_water_cleared_jpg,
                    GRID_SHIP_BOMBED: grid_ship_burning_jpg,
                    GRID_SHIP_BURNT: grid_ship_burnt_jpg
                }
                grid_image = switcher[data[row][col] % 10]  # select grid image based on the ones digit of grid value
                if grid_image:  # draw the grid image into that grid
                    game_image.paste(grid_image, offset)
    game_photo = ImageTk.PhotoImage(game_image)    # update game_photo to be shown


# load sound files
cur_directory = getcwd()
drum_up = cur_directory + "/drumup.wav"
launch_water = cur_directory + "/launch_water.wav"
launch_hit = cur_directory + "/launch_hit.wav"
launch_destroy = cur_directory + "/destroy.wav"
sound_to_play = drum_up


# thread class to play sound wave
class Thread_Sound(threading.Thread):
    def __init__(self, name):
        threading.Thread.__init__(self)
        self.name = name

    def run(self):
        global exiting, mute_flag, sound_to_play
        while not exiting:
            sound_playing = sound_to_play
            if sys.platform == 'win32':
                if not mute_flag:
                    winsound.PlaySound(sound_playing, winsound.SND_FILENAME)
                    if drum_up != sound_playing:
                        sound_to_play = drum_up
                else:
                    time.sleep(0.05)
            else:   # not tested path
                if not mute_flag:
                    os.system("afplay " + sound_playing)
                    if drum_up != sound_playing:
                        sound_to_play = drum_up
                else:
                    time.sleep(0.05)


class TimerThread(threading.Thread):
    def __init__(self):
        threading.Thread.__init__(self)
        self.stopFlag = False

    def run(self):
        while not self.stopFlag:
            time.sleep(1.0)
            seconds = time.time() - game_start_time  # game time in seconds
            time_string = "Time in game: " + time.strftime('%H:%M:%S', time.gmtime(seconds))
            if gaming:
                game_time_label.configure(text=time_string)
                game_time_label.update()

    def stop(self):
        self.stopFlag = True


def unmute_sound():
    global sound_thread, mute_flag
    mute_flag = False
    if not sound_thread:
        sound_thread = Thread_Sound("Sound")
        sound_thread.start()


def mute_sound():
    global sound_thread, mute_flag
    mute_flag = True
    if not sound_thread:
        sound_thread = Thread_Sound("Sound")
        sound_thread.start()


def on_exit():
    global sound_thread, exiting
    if sound_thread:    # shut down sound playing thread
        exiting = True
        sound_thread.join()
        sound_thread = None
    main_window.quit()  # kill GUI


def handle_keypress(event):
    if str(event.char).upper() == "Q":
        on_exit()
    elif str(event.char).upper() == "S":
        global game_cheat
        game_cheat = not game_cheat


# create main view
bg_color = '#195580'
main_window = ui.Tk()
main_window.title("Battleship War")
main_window.wm_attributes('-fullscreen', 'true')
main_window.configure(bg=bg_color)
# construct upper panel for main view
main_size = (main_window.winfo_screenwidth(), main_window.winfo_screenheight())
image_ocean = Image.open(cur_directory+"/ocean.jpg")
image_ocean = image_ocean.resize((main_size[0], round(main_size[1]*upper_fraction)), Image.BILINEAR)
image_upper = image_ocean.copy()
draw = ImageDraw.Draw(image_upper)
if sys.platform == 'win32':
    font = ImageFont.truetype("arial.ttf", size=96)
else:
    font = ImageFont.truetype("Keyboard.ttf", size=96)
draw.text((round(main_size[0]*0.30), round(main_size[1]*0.18)), "Welcome to\n\nBattleship War", (64, 0, 0, 32),
          font=font, align="center")
photo_upper = ImageTk.PhotoImage(image_upper)

upper_panel = ui.Label(master=main_window, image=photo_upper)
upper_panel.place(x=0, y=0, relwidth=1.0, relheight=upper_fraction)

main_window.bind("<Key>", handle_keypress)  # set handler for key press


# compute the number of missiles available based on player's skill selection
def on_skill():
    global missiles_total
    missiles_total = 50 - 5 * player_skill.get()


# construct middle panel for main view
player_skill = ui.IntVar(0)
missiles_total = 50
middle_panel = ui.Frame(master=main_window, bg=bg_color, padx=2, pady=2)
level_label = ui.Label(master=middle_panel, text="Please select your experience level", bg=bg_color,
                       font=("Courier", 32, 'bold')).grid(row=0, column=0, sticky="w")
ui.Radiobutton(master=middle_panel, text="Amateur - 45 missiles available", font=("Courier", 16, 'bold'), bg=bg_color,
               activebackground=bg_color, padx=50, variable=player_skill, value=0,
               command=on_skill).grid(row=1, column=0, columnspan=3, sticky="w")
ui.Radiobutton(master=middle_panel, text="Novice - 40 missiles available", font=("Courier", 16, 'bold'), bg=bg_color,
               activebackground=bg_color, padx=50, variable=player_skill, value=1,
               command=on_skill).grid(row=2, column=0, columnspan=3, sticky="w")
ui.Radiobutton(master=middle_panel, text="Intermediate - 35 missiles available", font=("Courier", 16, 'bold'),
               bg=bg_color, activebackground=bg_color, padx=50, variable=player_skill, value=2,
               command=on_skill).grid(row=3, column=0, columnspan=3, sticky="w")
ui.Radiobutton(master=middle_panel, text="Expert - 30 missiles available", font=("Courier", 16, 'bold'), bg=bg_color,
               activebackground=bg_color, padx=50, variable=player_skill, value=3,
               command=on_skill).grid(row=4, column=0, columnspan=3, sticky="w")
middle_panel.place(x=round(main_size[0]*0.25), y=round(main_size[1]*upper_fraction)+1,
                   relwidth=1.0, relheight=middle_fraction)


# handlers for game view
def game_keypress(event):
    if str(event.char).upper() == "Q":
        main_window.focus()


def handle_click(event):   # mouse click to launch missile if allowed
    if not gaming or not (game_mouse_x_min <= event.x <= game_mouse_x_max and
                          game_mouse_y_min <= event.y <= game_mouse_y_max):
        return    # click is not on the game board, ignore
    global game_missiles_label, game_hits_label, game_miss_label, game_missile_left, game_hits, game_miss

    row, col = mouse_in_grid(event.x, event.y)
    global game_data
    val = game_data[row][col]
    if val == GRID_WATER_CLEARED:
        return   # click is on cleared water, ignore

    if val % GRID_SHIP_SCALE == GRID_SHIP_BOMBED or val % GRID_SHIP_SCALE == GRID_SHIP_BURNT:
        return   # click is on ship already hit, ignore

    length = val // GRID_SHIP_SCALE   # calculate the ship length (tens digit)
    ship_hits = []   # list of hits the ship suffered so as to determine this is the last hit to sink the ship
    if val == GRID_WATER_FREE or val == GRID_WATER_OBSTRUCTED:  # hit water
        game_missile_left -= 1
        game_miss += 1
    elif val % GRID_SHIP_SCALE == GRID_SHIP_GOOD:    # hit ship
        game_missile_left -= 1
        game_hits += 1
        ship_hits.append((row, col))
        if length > 1:    # the ship length is more than one, find out all hits it suffered
            for idx in range(1, length):  # search the east direction
                if col+idx >= cols:   # stop at out of board
                    break
                elif game_data[row][col+idx] // GRID_SHIP_SCALE != length:  # not belong to this ship
                    break
                elif game_data[row][col+idx] // GRID_SHIP_SCALE == length and \
                        game_data[row][col+idx] % GRID_SHIP_SCALE == GRID_SHIP_BOMBED:
                    ship_hits.append((row, col+idx))    # belong to this ship and bombed
                else:
                    break
            for idx in range(1, length):  # search the west direction
                if col - idx < 0:
                    break
                elif game_data[row][col-idx] // GRID_SHIP_SCALE != length:
                    break
                elif game_data[row][col-idx] // GRID_SHIP_SCALE == length and \
                        game_data[row][col-idx] % GRID_SHIP_SCALE == GRID_SHIP_BOMBED:
                    ship_hits.append((row, col-idx))
                else:
                    break
            for idx in range(1, length):  # search the south direction
                if row+idx >= rows:
                    break
                elif game_data[row+idx][col] // GRID_SHIP_SCALE != length:
                    break
                elif game_data[row+idx][col] // GRID_SHIP_SCALE == length and \
                        (game_data[row+idx][col] % GRID_SHIP_SCALE) == GRID_SHIP_BOMBED:
                    ship_hits.append((row+idx, col))
                else:
                    break
            for idx in range(1, length):  # search the north direction
                if row - idx < 0:
                    break
                elif game_data[row-idx][col] // GRID_SHIP_SCALE != length:
                    break
                elif game_data[row-idx][col] // GRID_SHIP_SCALE == length and \
                        game_data[row-idx][col] % GRID_SHIP_SCALE == GRID_SHIP_BOMBED:
                    ship_hits.append((row-idx, col))
                else:
                    break

    global image_missiles, sound_to_play, mute_flag, hit_jpg, missed_jpg
    image_size = (100, 100)
    if not hit_jpg:   # load hit jpg and resize if not yet
        hit_jpg = Image.open(cur_directory + "/hit.jpg")
        hit_jpg = hit_jpg.resize(image_size, Image.BILINEAR)
    if not missed_jpg:  # load missed jpg and resize if not yet
        missed_jpg = Image.open(cur_directory + "/missed.jpg")
        missed_jpg = missed_jpg.resize(image_size, Image.BILINEAR)

    if len(image_missiles) == 0:  # load animation images if not yet
        for i in range(30):
            missile_image_name = cur_directory + "/frame" + str(i) + ".jpg"
            image = Image.open(missile_image_name)
            image = image.resize(image_size, Image.BILINEAR)
            image_missiles.append(image)
    missile_show = ui.Label(master=main_window)
    loc_x, loc_y = event.x, event.y
    if col == cols - 1:
        loc_x = int(loc_x - grid_width/2)
    if row == rows - 1:
        loc_y = int(loc_y - grid_height/2)
    missile_show.place(x=loc_x, y=loc_y)     # to display animation near mouse pointer
    time.sleep(1.0)    # give time to finish current sound wave
    if len(ship_hits) == 0:  # hit water
        game_data[row][col] = GRID_WATER_CLEARED   # update hit grid value
        sound_to_play = launch_water   # sound wave to play
        duration = 3.0   # sound duration
    elif len(ship_hits) < length:   # update hit grid value, hit the ship but not last hit
        game_data[row][col] = length*GRID_SHIP_SCALE + GRID_SHIP_BOMBED
        sound_to_play = launch_hit
        duration = 2.0
    else:  # last hit for the ship
        sound_to_play = launch_destroy
        global ships_sunken
        ships_sunken += 1      # sink a ship
        duration = 4.0
        for i in range(len(ship_hits)):
            row, col = ship_hits[i]
            game_data[row][col] = length*GRID_SHIP_SCALE + GRID_SHIP_BURNT
            water_cleared(row, col)

    if not mute_flag:
        unmute_sound()
    else:
        mute_sound()
    interval = (duration - 0.3)/30
    for i in range(30):    # animation of 30 frames
        photo_frame = ImageTk.PhotoImage(image_missiles[i])
        missile_show.configure(image=photo_frame)
        missile_show.update()
        time.sleep(interval)

    # last fame of animation, either hit or miss
    if game_data[row][col] == GRID_WATER_CLEARED:
        photo_frame = ImageTk.PhotoImage(missed_jpg)
    else:
        photo_frame = ImageTk.PhotoImage(hit_jpg)

    missile_show.configure(image=photo_frame)
    missile_show.update()
    time.sleep(0.3)

    missile_show.destroy()   # clear animation window
    draw_game(2)             # update the game board
    global game_upper_label
    game_upper_label.configure(image=game_photo)
    game_upper_label.place(x=0, y=0, relwidth=1.0, relheight=1.0)
    # update game information
    game_missiles_label.configure(text="Missiles(Available): "+str(game_missile_left))
    game_missiles_label.update()
    game_miss_label.configure(text="Missile Missed: "+str(game_miss))
    game_miss_label.update()
    game_ships_live_label.configure(text="Ships(to sink): "+str(ships_total-ships_sunken))
    game_ships_live_label.update()
    game_ships_sunken_label.configure(text="Ships Sunken: "+ str(ships_sunken))
    game_ships_sunken_label.update()

    # game over if ships are all hit or missiles are used up
    if game_hits == hits_needed or game_missile_left == 0:
        game_end()


def mouse_in_grid(x, y):  # convert mouse coordinate to board location
    x -= left_margin
    row, col = int(y)//int(line_width+grid_height), int(x)//int(line_width+grid_width)
    if row >= rows:
        row = rows - 1
    if col >= cols:
        col = cols - 1
    return row, col


def handle_mouse_move(event):  # update missile aiming location if within game board
    coord_text = ""
    if gaming and event.widget == game_upper_label and \
            game_mouse_x_min <= event.x <= game_mouse_x_max and game_mouse_y_min <= event.y <= game_mouse_y_max:
        row, col = mouse_in_grid(event.x, event.y)
        coord_text = "Aim at ({:1d},{:1d})".format(row, col)
    game_coord_label.configure(text=coord_text)
    game_coord_label.update()


def game_end():  # handle the end of game
    global sound_to_play, gaming
    gaming = False
    timer_thread.stop()   # stop timer thread
    game_duration_seconds = time.time() - game_start_time   # time spent on the game
    time_string = "\nTime in game: " + time.strftime('%H:%M:%S', time.gmtime(game_duration_seconds))
    if game_hits == hits_needed:
        message = "You Won!"
    elif game_missile_left == 0:
        message = "You Lost."
    else:
        message = "You Quit."
    message = message + time_string
    # display game ending message
    ui.Label(master=game_upper_panel, text=message, font=("Courier", 48, 'bold'))\
        .place(x=round(main_size[0] * 0.28), y=round(main_size[1] * 0.18))
    game_upper_panel.update()
    game_quit_button["state"] = "disabled"
    game_sound_button["state"] = "disabled"
    game_lower_panel.update()
    messagebox.showinfo(title=None, message=message)
    main_window.unbind("<Motion>")     # no longer track mouse motion
    main_window.unbind("<Button 1>")   # no longer track mouse click
    game_upper_panel.destroy()    # dismiss upper panel of game view
    game_middle_panel.destroy()   # dismiss middle panel of game view
    game_lower_panel.destroy()    # dismiss lower panel of game view
    main_window.bind("<Key>", handle_keypress)   # resume key press handler
    sound_to_play = drum_up       # play drum up sound in main view


def on_sound():    # sound on/off toggle handler in main view
    if mute_flag:
        sound_button['text'] = "Sound Off"
        mute_sound()
    else:
        sound_button['text'] = "Sound On"
        unmute_sound()
    sound_button.update()


def on_game_sound():  # sound on/off toggle handler in game view
    if not mute_flag:
        game_sound_button['text'] = "Sound Off"
        mute_sound()
    else:
        game_sound_button['text'] = "Sound On"
        unmute_sound()
    game_sound_button.update()


def start_play():  # Play button click handler to construct game and game view
    global game_photo, game_sound_button, game_upper_panel, game_middle_panel, game_lower_panel, mute_flag
    global game_upper_label, game_missile_left, game_hits, game_miss
    game_missile_left = missiles_total
    game_hits = 0
    game_miss = 0

    init_game()
    draw_game(1)

    game_color = bg_color
    # upper panel of game view
    game_upper_panel = ui.Frame(master=main_window, bg=game_color, padx=0, pady=0)
    game_upper_panel.place(x=0, y=0, relwidth=1.0, relheight=upper_fraction)
    game_upper_label = ui.Label(master=game_upper_panel)
    game_upper_label.configure(image=game_photo)
    game_upper_label.place(x=0, y=0, relwidth=1.0, relheight=1.0)
    main_window.bind("<Motion>", handle_mouse_move)  # set mouse motion handler
    game_upper_label.bind("<Button 1>", handle_click)  # set mouse click handler
    # construct middle panel of game view
    game_middle_panel = ui.Frame(master=main_window, bg=game_color, padx=2, pady=2)
    game_middle_panel.columnconfigure([0, 1, 2, 3, 4],  minsize=round(main_size[0] * 0.16), weight=1)
    game_middle_panel.rowconfigure([0, 1, 3, 4],  minsize=30, weight=1)
    global game_coord_label, game_missiles_label, game_ships_live_label, game_miss_label, game_ships_sunken_label
    game_coord_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color, activebackground=game_color,
                                text="", font=("Courier", 16, 'bold'), padx=20, pady=5)
    game_coord_label.grid(row=0, column=2, sticky="n")

    radar_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color, activebackground=game_color,
                           image=radar_photo, padx=20, pady=5)
    radar_label.grid(row=1, column=2, rowspan=2, sticky="n")

    game_missiles_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color, activebackground=game_color,
                                   text="Missiles(Available): "+str(game_missile_left),
                                   font=("Courier", 16, 'bold'), padx=20, pady=5)
    game_missiles_label.grid(row=1, column=1, sticky="w")
    game_ships_live_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color,
                                     activebackground=game_color, text="Ships(to sink): "+str(ships_total),
                                     font=("Courier", 16, 'bold'), padx=20, pady=5)
    game_ships_live_label.grid(row=2, column=1, sticky="w")

    game_miss_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color, activebackground=game_color,
                               text="Missile Missed: "+str(game_miss), font=("Courier", 16, 'bold'), padx=20, pady=5)
    game_miss_label.grid(row=1, column=3, sticky="w")
    game_ships_sunken_label = ui.Label(master=game_middle_panel, borderwidth=2, bg=game_color,
                                       activebackground=game_color, text="Ships Sunken: "+ str(ships_sunken),
                                       font=("Courier", 16, 'bold'), padx=20, pady=5)
    game_ships_sunken_label.grid(row=2, column=3, sticky="w")
    game_middle_panel.place(x=0, y=round(main_size[1] * upper_fraction) + 1, relwidth=1.0, relheight=middle_fraction)
    # lower panel of game view
    game_lower_panel = ui.Frame(master=main_window, bg=game_color, padx=0, pady=0)
    game_lower_panel.columnconfigure([0, 1, 2, 3], minsize=round(main_size[0] * 0.25), weight=1)
    global game_quit_button
    game_quit_button = ui.Button(master=game_lower_panel, width=8, borderwidth=2, bg=game_color,
                                 activebackground=game_color, font=("Courier", 16, 'bold'),
                                 text="Quit", command=game_end)
    game_quit_button.grid(row=0, column=2, sticky="e")
    global game_time_label
    game_time_label = ui.Label(master=game_lower_panel, borderwidth=2, bg=game_color,
                               activebackground=game_color, text="", font=("Courier", 16, 'bold'))
    game_time_label.grid(row=0, column=1, sticky="n")
    sound_text = "Sound On"
    if mute_flag:
        sound_text = "Sound Off"
    game_sound_button = ui.Button(master=game_lower_panel, width=10, borderwidth=2, bg=bg_color,
                                  activebackground=bg_color,
                                  font=("Courier", 16, 'bold'), text=sound_text, command=on_game_sound)
    game_sound_button.grid(row=0, column=3, sticky="n")
    game_lower_panel.place(x=0, y=round(main_size[1] * (1 - lower_fraction)) + 1,
                           relwidth=1.0, relheight=lower_fraction)
    main_window.unbind("<Key>")   # stop handle key press events
    global gaming, game_start_time, timer_thread
    gaming = True
    game_upper_panel.config(cursor="crosshair")
    game_start_time = time.time()
    timer_thread = TimerThread()
    timer_thread.start()


# lower panel of main view
lower_panel = ui.Frame(master=main_window, bg=bg_color, padx=0, pady=0)
lower_panel.columnconfigure([0, 1, 2], minsize=round(main_size[0]*0.33), weight=1)
ui.Button(master=lower_panel, width=8, borderwidth=2, bg=bg_color, activebackground=bg_color,
          font=("Courier", 16, 'bold'), text="Play", command=start_play).grid(row=0, column=0, sticky="e")
exit_button = ui.Button(master=lower_panel, width=8, borderwidth=2, bg=bg_color, activebackground=bg_color,
                        font=("Courier", 16, 'bold'), text="Exit", command=on_exit)
exit_button.grid(row=0, column=1, sticky="n")
lower_panel.place(x=0, y=round(main_size[1]*(1-lower_fraction))+1, relwidth=1.0, relheight=lower_fraction)


sound_button = ui.Button(master=lower_panel, width=10, borderwidth=2, bg=bg_color, activebackground=bg_color,
                         font=("Courier", 16, 'bold'), text="Sound On", command=on_sound)
sound_button.grid(row=0, column=2, sticky="w")
# app exit handler
main_window.protocol('WM_DELETE_WINDOW', on_exit)
main_window.mainloop()     # app main message loop until exit


