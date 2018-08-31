#!/usr/bin/python3
# ^^ note the python directive on the first line
# COMP 9414 agent initiation file 
# requires the host is running before the agent
# designed for python 3.6
# typical initiation would be (file in working directory, port = 31415)
#        python3 agent.py -p 31415
# created by Leo Hoare
# with slight modifications by Alan Blair
# 
# 
# 
# This is a group work. 
# Group members: Hu,Boxuan; Wang,Yan.
#   This program works with three parts: The first part is used for storing map information based on the agent's action.
#   The second part is used for searching a path based on the information of memorised map.
#   The third part is used for translating the path into a string and output the letter in this string one by one.
#     If this string is empty, we will use the second part to generate another path again.

# Working principle of the first part:
#   At first, we generate a initial map based on the data which we received from the host. 
#   After that, with the help of the function: expand_map()(line 194), we can expand the map which is memorised by the 
#   agent based on the action of agent. Different from the host's map, we use '?' to represent unexplored area, 
#   using '.' to represent the edge of map.
#   We also use some variables to records whether this agent have tools. For example, if the agent pick up a key,
#   self.have_key will become True.

# Working principle of the Second part:
#   This is the major part of this program. The agent searches the map with the use of BFS.
#   We choose the data structure deque to implement the BFS algorithm.
#   Firstly, we divide the state of agent into several parts such as
#   'the agent have no tools', 'the agent have stone only', etc.
#   For different state, we use different searching strategy to search a path.
#   In order to reduce more '?' in the map, once we find that there is '?' near a obstacle, we will let the agent go beside that obstacle.
  
#   At the beginning, the agent has no tools, the target of it is the '?', '$' or any other tools.
#   We use BFS starting with the location of the agent to search our target.
#   Once it finds the target, it will return a path consisting of coordinates.
#   If it finds '*', '~', '.', '-', 'T', it will find another way to bypass it.
#   if it finds '$', it will go there and pick up it and find a way back home.
  
#   Once the agent finds a tools, the searching strategy will change. 
#   At first, using the strategy which is used by having no tools. After that, check if the agent can search further with the help of its tools.
#   If the agent has key, it can open a door, so, if we use BFS and find '-', it will return a path to that door and open it. 
#   If the agent has an axe, it can cut down a tree, we use a function: find_target_tree() to decide which tree blocks our way to our target
#   (Our target is treasure, '?', and other resources). Once it find that tree, it will return a path to that tree and cut down it.
#   If the agent has stone, it can pass water, the strategy is as follow:
#      firstly, we search the path with using no stone, if it finds our target, it will return a path
#      then we search the path with using one stone, if it finds our target, it will return a path
#      then we search the path with using two stones, if it finds our target, it will return a path
#      so on and so forth, until we use all the stones which we have.
#   If the agent has raft, it can search on the water area, before we start searching in the water, we will decide which water can 
#   lead the agent to its target. (Which water can lead the agent to the '?' area or to the island which can lead agent to its target('?', '$')).
#   After making a decision, the agent will go to that water. If there isn't water area around, find another tree which is an obstacle and cut it down
#   to search further.
#   Once the agent find a '$', it will go and pick up it and find a way back home.
  
#   If the agent is sitting on a raft and searching in the sea. Firstly, if there is '?' area in the sea, we will let the agent to go there and
#   check it. Also, in order to reduce more '?' in the map, once we find that there is '?' near a obstacle, we will let the agent go beside that obstacle.
#   After we have already searched all the area in this water area, we will record the the information of each island, then the agent will make a decision
#   of landing based on the information of each island (line 3083): 
#       If an island has treasure and tree, we can land this island.
#       If an island has treasure and other resources, before we land it, we will check whether we can back home with the help of resources in that island.
#       If an island has resoruces only, before we land it, we will check whether we can go to our target when we land it. (If it can lead agent to '?', return True.
#           If it can lead agent to '$', checking if we can back home after we get that '$'. If we can back home, return True. Otherwise, return False.).
#       If there isn't any islands satisfy the conditions above, we choose an island which can lead agent to '?' area.
#       If there isn't any islands satisfy the conditions above, we choose an island which has the largest number of stones to land in.
#   If our landing point is 'T' or '-', we will find another landing point which is not an obstacle.

# Working principle of the Third part:
#   This part is used for translating the path (generated by the second part) into a commond string and output this string.(line 609 to line 692)
#   If the end of this path is a place we can get to, it just generate a commond string to that coordinate.
#   If the end of this path is not a place we can get to, it will generate a commond string to the second last coordinate and then
#   let the agent facing that coordinate.
  

import sys
import socket
import time
from collections import deque
from collections import defaultdict
from copy import deepcopy

# declaring visible grid to agent
view = [['' for _ in range(5)] for _ in range(5)]


class Agent:
    def __init__(self):
        self.list_of_direction = ['West', 'North', 'East', 'South']
        self.direction = 'North'
        self.map = deque()
        self.location = (3, 3)# initial position
        self.initial_location = [3, 3]
        self.searched_tree = defaultdict(list)

        self.have_key = False
        self.have_hammer = False
        self.have_raft = False
        self.list_of_trees_location = []# list of trees's location in current island.
        self.list_of_all_trees_location = []# list of trees' location in the whole map.
        self.list_of_all_stone_location = []
        self.list_of_all_key_locaton = []
        self.have_rock = [False, 0]
        self.sit_in_a_raft = False
        self.have_treasure = False
        self.have_searched_the_sea = False

    # find a tree in the land where the agent in.(update the location of the tree which we can walk to)
    def find_location_of_tree(self):
        self.list_of_trees_location = []
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(self.location)
        queue.appendleft([self.location])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*', '~', '-'}:
                    continue
                elif self.map[location[0]][location[1]] == 'T':
                    self.list_of_trees_location.append(location)
                    set_of_searched_point.add(location)
                    continue
                else:
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)

    def find_location_of_all_key(self):
        self.list_of_all_key_locaton = []
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] == 'k':
                    self.list_of_all_key_locaton.append((i, j))


    def find_location_of_all_tree(self):
        self.list_of_all_trees_location = []
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] == 'T':
                    self.list_of_all_trees_location.append((i, j))

    def find_location_of_all_stone(self):
        self.list_of_all_stone_location = []
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] == 'o':
                    self.list_of_all_stone_location.append((i, j))


    # find the set of locations which the initial location can walk to.
    def find_the_initial_land_area(self):
        set_of_searched_point = set()
        queue = deque()
        initial_location = (self.initial_location[0], self.initial_location[1])
        set_of_searched_point.add(initial_location)
        queue.appendleft([initial_location])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*', '~', '-', 'T'}:
                    continue
                elif self.map[location[0]][location[1]] in {'<', '>', '^', 'v'}:
                    if self.sit_in_a_raft:
                        continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

                else:
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
        return set_of_searched_point


    # find the island of this agent in.
    def find_this_island(self):
        if not self.sit_in_a_raft:
            set_of_searched_point = set()
            queue = deque()
            initial_location = self.location
            set_of_searched_point.add(initial_location)
            queue.appendleft([initial_location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*', '~', '-', 'T'}:
                        continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)
            return set_of_searched_point

    def update_search_tree(self):
        # add the point into our search tree.
        self.searched_tree = defaultdict(list)
        for i in range(1, len(self.map) - 1):
            for j in range(1, len(self.map[0]) - 1):
                if self.map[i][j] in {'?', '.', '*', '-'}:
                    continue
                else:
                    self.searched_tree[(i, j)] = [(i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)]

    def generate_initial_map(self, view):# generate the intial map.
        self.map.append(deque(['?','?','?','?','?','?','?']))
        for i in range(len(view)):
            one_list = deque(['?'])
            for j in range(len(view[0])):
                one_list.append(view[i][j])
            one_list.append('?')
            self.map.append(one_list)
        self.map.append(deque(['?','?','?','?','?','?','?']))
        self.update_search_tree()

    def find_position_of_agent(self):# find the position of agent located in memerised map
        sample_of_agent = {'>', '<','^', 'v'}
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] in sample_of_agent:
                    return (i, j)

    def change_direction(self, commond):# change direction of agent according to get_action()
        index_of_agent = self.location
        dic_of_direction = {'West': '<', 'North': '^', 'East': '>', 'South': 'v'}
        if commond in {'r', 'R'}:
            if self.list_of_direction.index(self.direction) != 3:
                self.direction = self.list_of_direction[self.list_of_direction.index(self.direction) + 1]
            else:
                self.direction = self.list_of_direction[0]
        elif commond in {'l', 'L'}:
            if self.list_of_direction.index(self.direction) != 0:
                self.direction = self.list_of_direction[self.list_of_direction.index(self.direction) - 1]
            else:
                self.direction = self.list_of_direction[3]
        self.map[index_of_agent[0]][index_of_agent[1]] = dic_of_direction[self.direction]

################################## change the environment of the memerised map. #############################


    def expand_map(self, commond, info, obstacle, left_thing):# change the environment of the memerised map.
        index_of_agent = self.location
        if commond in {'l', 'L', 'r', 'R'}:
            self.change_direction(commond)
            return


        if commond in {'f', 'F'}:
            # analyse the things before
            if obstacle == '.':# if we go over the edge, we will die....
                self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                self.location = None

            if obstacle == 'k':# if there is a key and we will forward, we will have a key.
                self.have_key = True

            if obstacle == 'a':# if there is a hammer and we will forward, we will have a hammer.
                self.have_hammer = True

            if obstacle == 'T':# if there is a tree, do nothing.
                return

            if obstacle == '$':# if there is a gold, we will have the treasure.
                self.have_treasure = True

            if obstacle == '*':# if there is a wall, do nothing.
                return

            if obstacle == '-':# if there is a door, do nothing.
                return

            if obstacle == '~' and ((not self.have_rock[0]) and (not self.have_raft) and (not self.sit_in_a_raft)):
                #if there is water and we don't have tools to go through it, we will die....
                self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                self.location = None
                return

            if obstacle == '~' and (not self.have_rock[0]) and (self.have_raft or self.sit_in_a_raft):
                # if there is water and we don't have rock but we have raft, we can search the water.
                # if there is water and we have rock, pass this 'if' and continue.
                self.have_raft = False
                self.sit_in_a_raft = True
                self.have_searched_the_sea = True

            if obstacle == '~' and self.have_rock[0]:
                # if there is water and we have rock, put it in the water.
                self.have_rock[1] -= 1
                if not self.have_rock[1]:
                    self.have_rock[0] = False

            if obstacle == ' ' and self.sit_in_a_raft:
                # if there is a land we we will land it, we will not have raft any more
                # and the state of sitting in a raft will change.
                self.have_raft = False
                self.sit_in_a_raft = False

            if obstacle == 'o':
                # it the stone is not the one which is being used, pick it up.
                # if the stone is in the water, walk through it.
                self.have_rock[0] = True
                self.have_rock[1] += 1



            if self.direction == 'North':# go up
                list_tobe_changed = set()
                for i in range(index_of_agent[1] - 2, index_of_agent[1] + 3):
                    list_tobe_changed.add(self.map[index_of_agent[0] - 3][i])

                if '?' in list_tobe_changed and index_of_agent[0] - 4 >= 0:# doesn't over edge, just change environment.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] - 3][index_of_agent[1] - 2 + i] = info[i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] - 1][index_of_agent[1]] = '^'
                    self.location = (index_of_agent[0] - 1, index_of_agent[1])
                    self.map[self.location[0] + 1][self.location[1]] = left_thing
                    return
                if '?' in list_tobe_changed and index_of_agent[0] - 4 < 0:# over the top edge, need to expand
                    width_of_map = len(self.map[0])
                    for i in range(len(info)):
                        self.map[index_of_agent[0] - 3][index_of_agent[1] - 2 + i] = info[i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] - 1][index_of_agent[1]] = '^'
                    first_row = deque(['?' for _ in range(width_of_map)])
                    self.map.appendleft(first_row)
                    self.initial_location[0] += 1
                    self.map[self.location[0] + 1][self.location[1]] = left_thing
                    return
                else:# do not have any mist, just go forward.
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] - 1][index_of_agent[1]] = '^'
                    self.location = (index_of_agent[0] - 1, index_of_agent[1])
                    self.map[self.location[0] + 1][self.location[1]] = left_thing
                    return



            if self.direction == 'South':# go down

                list_tobe_changed = set()
                for i in range(index_of_agent[1] - 2, index_of_agent[1] + 3):
                    list_tobe_changed.add(self.map[index_of_agent[0] + 3][i])
                height = len(self.map)
                if '?' in list_tobe_changed and index_of_agent[0] + 4 <= height - 1:# doesn't over edge, just change environment.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 3][index_of_agent[1] - 2 + i] = info[4 - i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] + 1][index_of_agent[1]] = 'v'
                    self.location = (index_of_agent[0] + 1, index_of_agent[1])
                    self.map[self.location[0] - 1][self.location[1]] = left_thing
                    return
                if '?' in list_tobe_changed and index_of_agent[0] + 4 > height - 1:# over the down edge, need to expand.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 3][index_of_agent[1] - 2 + i] = info[4 - i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] + 1][index_of_agent[1]] = 'v'
                    added_row = deque(['?' for _ in range(len(self.map[0]))])
                    self.map.append(added_row)
                    self.location = (index_of_agent[0] + 1, index_of_agent[1])
                    self.map[self.location[0] - 1][self.location[1]] = left_thing
                    return
                else:# do not have any mist, just go forward.
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0] + 1][index_of_agent[1]] = 'v'
                    self.location = (index_of_agent[0] + 1, index_of_agent[1])
                    self.map[self.location[0] - 1][self.location[1]] = left_thing
                    return


            if self.direction == 'West':# go west

                list_tobe_changed = set()
                for i in range(index_of_agent[0] + 2, index_of_agent[0] - 3, -1):
                    list_tobe_changed.add(self.map[i][index_of_agent[1] - 3])
                if '?' in list_tobe_changed and index_of_agent[1] - 4 >= 0:# doesn't over edge, just change environment.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 2 - i][index_of_agent[1] - 3] = info[i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] - 1] = '<'
                    self.location = (index_of_agent[0], index_of_agent[1] - 1)
                    self.map[self.location[0]][self.location[1] + 1] = left_thing
                    return
                if '?' in list_tobe_changed and index_of_agent[1] - 4 < 0:# over the down edge, need to expand.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 2 - i][index_of_agent[1] - 3] = info[i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] - 1] = '<'
                    for i in range(len(self.map)):
                        self.map[i].appendleft('?')
                    self.initial_location[1] += 1
                    self.map[self.location[0]][self.location[1] + 1] = left_thing
                    return
                else:# do not have any mist, just go forward.
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] - 1] = '<'
                    self.location = (index_of_agent[0], index_of_agent[1] - 1)
                    self.map[self.location[0]][self.location[1] + 1] = left_thing
                    return

            if self.direction == 'East':# go east

                list_tobe_changed = set()
                for i in range(index_of_agent[0] + 2, index_of_agent[0] - 3, -1):
                    list_tobe_changed.add(self.map[i][index_of_agent[1] + 3])
                width = len(self.map[0])
                if '?' in list_tobe_changed and index_of_agent[1] + 4 <= width - 1:# doesn't over edge, just change environment.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 2 - i][index_of_agent[1] + 3] = info[4 - i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] + 1] = '>'
                    self.location = (index_of_agent[0], index_of_agent[1] + 1)
                    self.map[self.location[0]][self.location[1] - 1] = left_thing
                    return
                if '?' in list_tobe_changed and index_of_agent[1] + 4 > width - 1:# over the down edge, need to expand.
                    for i in range(len(info)):
                        self.map[index_of_agent[0] + 2 - i][index_of_agent[1] + 3] = info[4 - i]
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] + 1] = '>'
                    for i in range(len(self.map)):
                        self.map[i].append('?')
                    self.location = (index_of_agent[0], index_of_agent[1] + 1)
                    self.map[self.location[0]][self.location[1] - 1] = left_thing
                    return
                else:# do not have any mist, just go forward.
                    self.map[index_of_agent[0]][index_of_agent[1]] = ' '
                    self.map[index_of_agent[0]][index_of_agent[1] + 1] = '>'
                    self.location = (index_of_agent[0], index_of_agent[1] + 1)
                    self.map[self.location[0]][self.location[1] - 1] = left_thing
                    return

        if commond in {'c', 'C'}:
            if obstacle != 'T' or not self.have_hammer:
                # if there isn't a tree in the front or we do not have a hammer, do nothing.
                return
            # checking the direction.
            # Once we cut down a tree, we will have a raft.
            if self.direction == 'North':
                self.map[self.location[0] - 1][self.location[1]] = ' '
                self.have_raft = True
                return
            if self.direction == 'South':
                self.map[self.location[0] + 1][self.location[1]] = ' '
                self.have_raft = True
                return
            if self.direction == 'East':
                self.map[self.location[0]][self.location[1] + 1] = ' '
                self.have_raft = True
                return
            if self.direction == 'West':
                self.map[self.location[0]][self.location[1] - 1] = ' '
                self.have_raft = True
                return

        if commond in {'u', 'U'}:
            if obstacle != '-' or not self.have_key:
                # if there isn't a door or we do not have a key, do nothing.
                return
            # otherwise, checking the direction.
            if self.direction == 'North':
                self.map[self.location[0] - 1][self.location[1]] = ' '
                return
            if self.direction == 'South':
                self.map[self.location[0] + 1][self.location[1]] = ' '
                return
            if self.direction == 'East':
                self.map[self.location[0]][self.location[1] + 1] = ' '
                return
            if self.direction == 'West':
                self.map[self.location[0]][self.location[1] - 1] = ' '
                return

#############################################################################################################

    ################################# helpful function #############################

    def neighbour_of_point(self, point):
        return [(point[0] - 1, point[1]), (point[0] + 1, point[1]), (point[0], point[1] - 1), (point[0], point[1] + 1)]

    def is_mist_area_around(self, point):
        for i in range(-1, 2):
            for j in range(-1, 2):
                if i == j:
                    continue
                if self.map[point[0] - i][point[1] - j] == '?':
                    return True
        return False

    def is_neighbour(self, point_1, point_2):
        distance = self.distance_of_two_point(point_1, point_2)
        if distance > 1:
            return False
        else:
            return True

    # search the area which we haven't explored, find if there is a mist.
    # it there is a mist, return True. Else, return False.
    def is_real_target_tree(self, location, this_tree):
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(location)
        set_of_searched_point.add(this_tree)
        queue.appendleft([location])
        if self.map[location[0]][location[1]] not in {'?'}:# if itself is not a mist.
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for points in self.searched_tree[operate_location]:
                    if (points in set_of_searched_point) or self.map[points[0]][points[1]] in {'*', '.'}:
                        continue
                    elif self.map[points[0]][points[1]] == '$':# if there is a treasure. return True.
                        return True
                    else:
                        add_list = operate_list + [points]
                        queue.appendleft(add_list)
                        set_of_searched_point.add(points)
            # if there isn't any treasure, find if there is a resources.
            set_of_searched_point = set()
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for points in self.searched_tree[operate_location]:
                    if (points in set_of_searched_point) or self.map[points[0]][points[1]] in {'*', '.'}:
                        continue
                    elif self.map[points[0]][points[1]] == 'k':# if there is resources. return True.
                        if not self.key:
                            return 'Yes'
                    elif self.map[points[0]][points[1]] == 'o':
                        return 'Yes'
                    else:
                        add_list = operate_list + [points]
                        queue.appendleft(add_list)
                        set_of_searched_point.add(points)
            # if there isn't any resources, find if there is a mist.
            set_of_searched_point = set()
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for points in self.searched_tree[operate_location]:
                    if (points in set_of_searched_point) or self.map[points[0]][points[1]] in {'*', '.'}:
                        continue
                    elif self.map[points[0]][points[1]] == '?':# if there is resources. return True.
                        'Possible'
                    else:
                        add_list = operate_list + [points]
                        queue.appendleft(add_list)
                        set_of_searched_point.add(points)

    # find the target tree to cut down.
    def find_target_tree(self, set_of_searched_path):
        self.find_location_of_tree()
        if self.list_of_trees_location == []:# if there isn't a tree, game failed.
            return
        else:
            target_tree = (0, False)
            second_target_tree = (0, False)
            for location in self.list_of_trees_location:
                neighbour_list = self.neighbour_of_point(location)
                for neigh in neighbour_list:
                    if (neigh not in set_of_searched_path) and (self.map[neigh[0]][neigh[1]] not in {'*', '~', '.'}):
                        # if one of the unexplored point is not a wall or water.
                        double_check = self.is_real_target_tree(neigh, location)
                        if double_check == 'Possible':
                            target_tree = (location, 'Possible')
                            continue

                        if double_check == 'Yes':# continue, check another possible exit.
                            target_tree = (location, 'Yes')
                            return target_tree

                        if double_check == True:
                            target_tree = (location, True)
                            return target_tree

            # If we couldn't find the best obstacle tree, find another possible obstacle tree.
            if not target_tree[0]:
                for location in self.list_of_trees_location:
                    neighbour_list = self.neighbour_of_point(location)
                    for neigh in neighbour_list:
                        if (neigh not in set_of_searched_path) and (self.map[neigh[0]][neigh[1]] not in {'*', '.'}):
                            # if one of the unexplored point is not a wall.
                            double_check = self.is_real_target_tree(neigh, location)
                            if double_check == 'Possible':
                                second_target_tree = (location, 'Possible')
                                continue

                            if double_check == 'Yes':# continue, check another possible exit.
                                target_tree = (location, 'Yes')
                                return target_tree

                            if double_check == True:
                                second_target_tree = (location, True)
                                return second_target_tree

            if target_tree[1] == 'Possible':
                return target_tree
            if second_target_tree[1] == 'Possible':
                return second_target_tree
            else:
                return (self.list_of_trees_location[0], 'Random')# Let the god to make a decision.


    def decide_direction(self, present_tuple, target_tuple):
        if target_tuple[0] - present_tuple[0] == 1 and target_tuple[1] == present_tuple[1]:
            return 'South'
        if target_tuple[0] - present_tuple[0] == -1 and target_tuple[1] == present_tuple[1]:
            return 'North'
        if target_tuple[0] == present_tuple[0] and target_tuple[1] - present_tuple[1] == 1:
            return 'East'
        if target_tuple[0] == present_tuple[0] and target_tuple[1] - present_tuple[1] == -1:
            return 'West'

    def decode_two_direction_into_commond(self, present_direction, target_direction):
        if present_direction == 'North':
            if target_direction == 'North':
                return 'f'
            if target_direction == 'South':
                return 'rrf'
            if target_direction == 'East':
                return 'rf'
            if target_direction == 'West':
                return 'lf'
        if present_direction == 'South':
            if target_direction == 'North':
                return 'llf'
            if target_direction == 'South':
                return 'f'
            if target_direction == 'East':
                return 'lf'
            if target_direction == 'West':
                return 'rf'
        if present_direction == 'East':
            if target_direction == 'North':
                return 'lf'
            if target_direction == 'South':
                return 'rf'
            if target_direction == 'East':
                return 'f'
            if target_direction == 'West':
                return 'rrf'
        if present_direction == 'West':
            if target_direction == 'North':
                return 'rf'
            if target_direction == 'South':
                return 'lf'
            if target_direction == 'East':
                return 'llf'
            if target_direction == 'West':
                return 'f'
    

    #translate the list of location into a string of commond
    def decode_location_into_string(self, _tuple):
        path = _tuple[0]
        target = _tuple[1]
        direction = self.direction
        out_put_string = ''

        if target == 0:
            for i in range(len(path) - 1):
                present_tuple = path[i]
                target_tuple = path[i + 1]
                target_direction = self.decide_direction(present_tuple, target_tuple)# find next direction
                out_put_string += self.decode_two_direction_into_commond(direction, target_direction)
                direction = target_direction
            return out_put_string
        else:
            for i in range(len(path) - 1):
                present_tuple = path[i]
                target_tuple = path[i + 1]
                target_direction = self.decide_direction(present_tuple, target_tuple)# find next direction
                out_put_string += self.decode_two_direction_into_commond(direction, target_direction)
                direction = target_direction
            if len(path) != 1:
                target_direction = self.decide_direction(target_tuple, target)
                # don't go forward, just look at it!!!
                add_str = self.decode_two_direction_into_commond(direction, target_direction)[: -1]
                out_put_string += add_str
                return out_put_string
            else:
                target_direction = self.decide_direction(path[0], target)
                add_str = self.decode_two_direction_into_commond(direction, target_direction)[: -1]
                out_put_string += add_str
                return out_put_string


#############################################################################################################


################## Using BFS to find a possible path to explore the map as far as possible. ##############
    
    #### This function is used for catching the treasure. ####
    # this is only used for the condition that we don't have stone.
    def catch_treasure(self):
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(self.location)
        queue.appendleft([self.location])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if location in set_of_searched_point or self.map[location[0]][location[-1]] in {'.', '*', 'T', '-', '~'}:
                    continue
                elif self.map[location[0]][location[-1]] == '$':
                    add_list = operate_list + [location]
                    out_put_string = self.decode_location_into_string((add_list, 0))
                    return out_put_string
                else:
                    add_list = operate_list + [(location[0], location[1])]
                    set_of_searched_point.add(add_list[-1])
                    queue.appendleft(add_list)


    #### This function is used for the condition that we have no tools.  ####
    def search_path_no_tools(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]

            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a'}:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.

                for location in self.searched_tree[operate_location]:# four possible path.
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T', '-', '~'}):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':# if we already find a gold. pick it
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string


                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]

            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a'}:
                # if we find a path to go, return that path.
                # which means operate_list[-1] is the location which we want to go,
                # we can go to the position which located before it to check if it is safe.
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string
                else:
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string
            # if we already find every path.
            else:
                return

        # if we have found treasure, just go back.
        else:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:

                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        continue
                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)




#############################################################################################################

    ##### This function is used for the condition that we only have key. ####
    def search_path_have_key(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]


            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a', '-'}:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.

                for location in self.searched_tree[operate_location]:# four possible path.
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T', '~'}):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':# if we already find a gold. pick it
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]

            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a', '-'}:
                # if we find a path to go, return that path.
                # which means operate_list[-1] is the location which we want to go,
                # we can go to the position which located before it to check if it is safe.
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string

                # if we find a door, go there and use a key.
                elif self.map[operate_list[-1][0]][operate_list[-1][1]] == '-':
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    out_put_string += 'u'
                    return out_put_string

                else:
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string
            # if we already find every path.
            else:
                return
        # if we have found the treasure.
        else:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        continue
                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)



#############################################################################################################
    #### This function is used for the condition that we only have axe. #####
    def search_path_with_hammer(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]


            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a'}:# we don't have key
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                # Because maybe we could use another tree, wo must first search the area as far as possible and decide which
                # tree could be the best one for us to cut down.
                for location in self.searched_tree[operate_location]:# four possible path.
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T', '-', '~'}):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]

            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a'}:
                # if we find a path to go, return that path.
                # which means operate_list[-1] is the location which we want to go,
                # we can go to the position which located before it to check if it is safe.
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string

                else:
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string
            # if we already find every path, find if there is a tree.
            else:
                self.find_location_of_tree()
                target_tree = self.find_target_tree(set_of_searched_path)
                # search a path to go to that target_tree.
                if target_tree != None:
                    set_of_searched_path = set()
                    queue = deque()
                    set_of_searched_path.add((self.location[0], self.location[1]))
                    operate_list = [(self.location[0], self.location[1])]
                    operate_location = operate_list[-1]
                    while operate_location != target_tree[0]:
                        for location in self.searched_tree[operate_location]:
                            if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', '-', '~'}):
                                continue
                            if self.map[location[0]][location[1]] == 'T':
                                if location == target_tree[0]:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                                else:
                                    continue
                            else:
                                add_list = operate_list + [(location[0], location[1])]
                                set_of_searched_path.add(add_list[-1])
                                queue.appendleft(add_list)
                        if len(queue) == 0:
                            break
                        operate_list = queue.pop()
                        operate_location = operate_list[-1]

                    if operate_location != target_tree[0]:
                        return
                    else:
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        out_put_string += 'c'
                        return out_put_string
        # if we have found the treasure.
        else:
            # judge if we can go back without using raft.
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        continue
                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)

            # if not, search the area until we find a tree.
            self.update_search_tree()
            self.find_location_of_tree()
            target_tree = self.find_target_tree(set_of_searched_path)

            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', '-', '~'}:
                        continue

                    # firstly, find if there is stone or key in this area.
                    elif self.map[location[0]][location[1]] in {'o', 'k'}:
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    # find if there is a tree.
                    elif self.map[location[0]][location[1]] == 'T':
                        if location != target_tree[0]:
                            continue
                        else:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'c'
                            return out_put_string

                    # find if there is a mist.
                    elif self.map[location[0]][location[1]] == '?':
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        return out_put_string

                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)



#############################################################################################################

    #### This function is used for the condition that we only have Stone. #####
    
    # firstly, we search the path with using no stone, go as far as we can.
    # then we search the path with using one stone, go as far as we can,
    # then we search the path with using tow stone, go as far as we can,
    # so on and so forth.

    def search_path_with_stone(self):
        if not self.have_treasure:
            number_of_stone = self.have_rock[1]
            self.update_search_tree()
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)

                while len(queue) != 0:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.' or location in set_of_searched_path:
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif self.map[location[0]][location[1]] in {'*', 'T'}:
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue

                        elif self.map[location[0]][location[1]] == '$':
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])
        
        else:
            # judge if we can go back without using extra stone.
            self.update_search_tree()
            birth_land = self.find_the_initial_land_area()
            number_of_stone = self.have_rock[1]
            for i in range(number_of_stone + 1):
                self.update_search_tree()
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                down_water = False
                set_of_searched_path.add((self.location[0], self.location[1]))
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]

                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] in {'.', '*', 'T', '-', '?'} or (location in set_of_searched_path):
                            continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif location == (self.initial_location[0], self.initial_location[1]):
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])

            # if not, find enough resource as much as possible.
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                down_water = False

                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.':
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            left_stone = i - time_of_cross_water
                            New_down_water = True
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T'}):
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue


                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            set_of_searched_path.add(location)
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])



#############################################################################################################

    #### This function is used for the condition that we have Stone and have key. #####
    
    # This state is equivalent to have stone and we can open a door.
    
    def search_path_with_stone_key(self):
        if not self.have_treasure:
            number_of_stone = self.have_rock[1]
            self.update_search_tree()
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)

                while len(queue) != 0:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.' or location in set_of_searched_path:
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif self.map[location[0]][location[1]] in {'*', 'T'}:
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue

                        elif self.map[location[0]][location[1]] == '-':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            out_put_string += 'u'
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '$':
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])
        
        else:
            # judge if we can go back without using extra stone.
            self.update_search_tree()
            birth_land = self.find_the_initial_land_area()
            number_of_stone = self.have_rock[1]
            for i in range(number_of_stone + 1):
                self.update_search_tree()
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                down_water = False
                set_of_searched_path.add((self.location[0], self.location[1]))
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]

                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] in {'.', '*', 'T', '-', '?'} or (location in set_of_searched_path):
                            continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif location == (self.initial_location[0], self.initial_location[1]):
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])

            # if not, find enough resource as much as possible.
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                down_water = False

                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.':
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            left_stone = i - time_of_cross_water
                            New_down_water = True
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T'}):
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue

                        elif self.map[location[0]][location[1]] == '-':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            out_put_string += 'u'
                            return out_put_string

                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            set_of_searched_path.add(location)
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])

#############################################################################################################

    #### This function is used for the condition that we have Axe and have key. #####

    # This state is equivalent to have Axe and we can open a door.
    
    def search_path_with_hammer_key(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]


            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a', '-'}:# we have key
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                # Because maybe we could use another tree, wo must first search the area as far as possible and decide which
                # tree could be the best one for us to cut down.
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.' or (location in set_of_searched_path):
                        continue

                    elif self.map[location[0]][location[1]] == '$':
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    elif self.map[location[0]][location[1]] in {'*', 'T', '~'}:
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]

            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a', '-'}:
                # if we find a path to go, return that path.
                # which means operate_list[-1] is the location which we want to go,
                # we can go to the position which located before it to check if it is safe.
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string

                elif self.map[operate_list[-1][0]][operate_list[-1][1]] == '?':
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string

                elif self.map[operate_list[-1][0]][operate_list[-1][1]] == '-':
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    out_put_string += 'u'
                    return out_put_string

            # if we already find every path, find if there is a tree.
            else:
                self.find_location_of_tree()
                target_tree = self.find_target_tree(set_of_searched_path)
                # search a path to go to that target_tree.
                if target_tree != None:
                    set_of_searched_path = set()
                    queue = deque()
                    set_of_searched_path.add((self.location[0], self.location[1]))
                    operate_list = [(self.location[0], self.location[1])]
                    operate_location = operate_list[-1]
                    while operate_location != target_tree[0]:
                        for location in self.searched_tree[operate_location]:
                            if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', '-', '~'}):
                                continue
                            if self.map[location[0]][location[1]] == 'T':
                                if location == target_tree[0]:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                                else:
                                    continue
                            else:
                                add_list = operate_list + [(location[0], location[1])]
                                set_of_searched_path.add(add_list[-1])
                                queue.appendleft(add_list)
                        if len(queue) == 0:
                            break
                        operate_list = queue.pop()
                        operate_location = operate_list[-1]

                    if operate_location != target_tree[0]:
                        return
                    else:
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        out_put_string += 'c'
                        return out_put_string
        
        # if we have found treasure.
        else:
            # firstly, find a way to home.
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        continue
                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)

            # if not, search the area until we find a tree.
            self.update_search_tree()
            self.find_location_of_tree()
            target_tree = self.find_target_tree(set_of_searched_path)

            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', '~'}:
                        continue

                    elif self.map[location[0]][location[1]] == '-':
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        out_put_string += 'u'
                        return out_put_string

                    # firstly, find if there is stone or key in this area.
                    elif self.map[location[0]][location[1]] in {'o', 'k'}:
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    # find if there is a tree.
                    elif self.map[location[0]][location[1]] == 'T':
                        if location != target_tree[0]:
                            continue
                        else:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'c'
                            return out_put_string
                    # find if there is a mist.
                    elif self.map[location[0]][location[1]] == '?':
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        return out_put_string

                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)



#############################################################################################################

    #### This function is used for find the all the island area which have stones and trees. #####
    # this function will output a list of island information: [{points in this island}, nb of stone which we can see, if it has tree, if it has key]
    
    def find_all_stone_island(self):
        self.find_location_of_all_stone()
        self.find_location_of_all_tree()
        self.find_location_of_all_key()
        list_of_stone_island = []# output list
        set_of_searched_point = set()
        # add stone island
        for stones in self.list_of_all_stone_location:
            if stones in set_of_searched_point:
                continue
            else:
                if self.map[stones[0]][stones[1]] == 'o':
                    count_of_stone = 1
                else:
                    count_of_stone = 0
                have_tree = False
                have_key = False
                queue = deque()
                set_of_this_island = set()
                queue.appendleft([stones])
                set_of_this_island.add(stones)
                set_of_searched_point.add(stones)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if location in set_of_this_island or self.map[location[0]][location[1]] in {'~', '*', '.', '?'}:
                            continue
                        elif self.map[location[0]][location[1]] in {'>', '<', '^', 'v'}:
                            if self.sit_in_a_raft:
                                continue
                            else:
                                set_of_searched_point.add(location)
                                add_list = operate_list + [location]
                                queue.appendleft(add_list)
                        elif self.map[location[0]][location[1]] == 'o':
                            count_of_stone += 1
                            add_list = operate_list + [location]
                            set_of_this_island.add(location)
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
                        elif self.map[location[0]][location[1]] == 'T':
                            have_tree = True
                            add_list = operate_list + [location]
                            set_of_this_island.add(location)
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
                        elif self.map[location[0]][location[1]] == 'k':
                            have_key = True
                            add_list = operate_list + [location]
                            set_of_this_island.add(location)
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
                        elif self.map[location[0]][location[1]] == '-':
                            if not self.have_key:
                                continue
                            else:
                                add_list = operate_list + [location]
                                set_of_this_island.add(location)
                                set_of_searched_point.add(location)
                                queue.appendleft(add_list)
                        else:
                            add_list = operate_list + [location]
                            set_of_this_island.add(location)
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
                list_of_stone_island.append((set_of_this_island, count_of_stone, have_tree, have_key))
        # add tree island
        for trees in self.list_of_all_trees_location:
            if trees in set_of_searched_point:
                continue
            else:
                have_tree = True
                have_key = False
                queue = deque()
                set_of_this_island = set()
                queue.appendleft([trees])
                set_of_this_island.add(trees)
                set_of_searched_point.add(trees)
                count_of_stone = 0
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if location in set_of_this_island or self.map[location[0]][location[1]] in {'*', '~', '.', '?'}:
                            continue

                        elif self.map[location[0]][location[1]] in {'>', '<', '^', 'v'}:
                            if self.sit_in_a_raft:
                                continue
                            else:
                                set_of_searched_point.add(location)
                                set_of_this_island.add(location)
                                add_list = operate_list + [location]
                                queue.appendleft(add_list)

                        elif self.map[location[0]][location[1]] == '-':
                            if not self.key:
                                continue
                            set_of_searched_point.add(location)
                            set_of_this_island.add(location)
                            add_list = operate_list + [location]
                            queue.appendleft(add_list)
                        elif self.map[location[0]][location[1]] == 'k':
                            have_key = True
                            add_list = operate_list + [location]
                            set_of_this_island.add(location)
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
                        else:
                            set_of_searched_point.add(location)
                            set_of_this_island.add(location)
                            add_list = operate_list + [location]
                            queue.appendleft(add_list)
                list_of_stone_island.append((set_of_this_island, count_of_stone, have_tree, have_key))
        # add key island.
        for keys in self.list_of_all_key_locaton:
            if keys in set_of_searched_point:
                continue
            else:
                have_key = True
                queue = deque()
                set_of_this_island = set()
                queue.appendleft([keys])
                set_of_this_island.add(keys)
                set_of_searched_point.add(keys)
                count_of_stone = 0
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if location in set_of_this_island or self.map[location[0]][location[1]] in {'*', '~', '.', '?'}:
                            continue

                        elif self.map[location[0]][location[1]] in {'>', '<', '^', 'v'}:
                            if self.sit_in_a_raft:
                                continue
                            else:
                                set_of_searched_point.add(location)
                                set_of_this_island.add(location)
                                add_list = operate_list + [location]
                                queue.appendleft(add_list)

                        elif self.map[location[0]][location[1]] == '-':
                            if not self.key:
                                continue
                            set_of_searched_point.add(location)
                            set_of_this_island.add(location)
                            add_list = operate_list + [location]
                            queue.appendleft(add_list)
                        else:
                            set_of_searched_point.add(location)
                            set_of_this_island.add(location)
                            add_list = operate_list + [location]
                            queue.appendleft(add_list)
                list_of_stone_island.append((set_of_this_island, count_of_stone, have_tree, have_key))

        return list_of_stone_island


#############################################################################################################

    #### This function is used for find the water which can land in birth island. #####
    
    def find_backhome_water(self, point):
        self.update_search_tree()
        set_of_birth_land = self.find_the_initial_land_area()# the birth island.
        set_of_this_water = set()
        queue = deque()
        set_of_this_water.add(point)
        queue.appendleft([point])
        # if we cannot back home with only trees, we will find stone.
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if self.map[location[0]][location[1]] in {'.', '*'} or location in set_of_this_water:
                    continue
                elif self.map[location[0]][location[1]] in {'<', '>', '^', 'v'}:
                    continue

                elif self.map[location[0]][location[1]] != '~':
                    if self.back_home_stone_island(location):
                        return True
                    else:
                        continue
                else:
                    add_list = operate_list + [location]
                    set_of_this_water.add(add_list[-1])
                    queue.appendleft(add_list)


#############################################################################################################

    #### This function: if this stone island can take us to home. #####
    
    def back_home_stone_island(self, point):
        self.update_search_tree()
        set_of_birth_land = self.find_the_initial_land_area()
        list_of_tree_stone_island = self.find_all_stone_island()# the island have stone.
        location_of_this_land = set()
        if point in set_of_birth_land:# if this land is the birth land, return true.
            return True
        nb_of_stone = 0
        have_tree = False
        rafting = False
        have_key = self.have_key
        queue = deque()
        down_water = False
        for tuples in list_of_tree_stone_island:
            if point in tuples[0]:
                nb_of_stone = tuples[1]
                have_tree = tuples[2]
                if not have_key:
                    have_key = tuples[3]
                location_of_this_land = tuples[0]# this island.
        if nb_of_stone == 0 and have_tree == False and have_key == False:# if this island does not have tree or stone or key.
            return False
        set_of_searched_point = set()
        set_of_searched_point.add(point)
        queue.appendleft([[point], nb_of_stone, have_tree, have_key, rafting, down_water])# path, nb_of_stone, can go through water, if has key.
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_path = operate_list[0]
            nb_of_stone = operate_list[1]
            have_tree = operate_list[2]
            have_key = operate_list[3]
            rafting = operate_list[4]
            N_down_water = operate_list[5]
            for location in self.searched_tree[operate_path[-1]]:
                if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*'}:
                    continue
                elif self.map[location[0]][location[1]] == '?':
                    continue
                elif location == (self.initial_location[0], self.initial_location[1]):# if we found the birth point.
                    return True
                if self.sit_in_a_raft:
                    if self.map[location[0]][location[1]] in {'~', '<', '>', '^', 'v'}:# if in the water
                        New_down_water = True
                        if nb_of_stone > 0:# if have stone, using stone firstly
                            if location in set(operate_path):
                                continue
                            new_stone = nb_of_stone - 1
                            add_path = operate_path + [location]
                            queue.appendleft([add_path, new_stone, have_tree, have_key, rafting, New_down_water])
                        elif nb_of_stone == 0:
                            if have_tree or rafting:# if we don't have stone, using tree.
                                have_tree = False
                                rafting = True
                                add_path = operate_path + [location]
                                set_of_searched_point.add(location)
                                queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, New_down_water])
                    elif self.map[location[0]][location[1]] != '~':# if we land in again.
                        if location == (self.initial_location[0], self.initial_location[1]):# if we found the birth point.
                            return True

                        elif location in location_of_this_land:# if the land is the location of this land.
                            if location in set(operate_path):
                                continue
                            add_path = operate_path + [location]
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        elif self.map[location[0]][location[1]] == '-':
                            if not have_key:# if this path do not have key.
                                continue
                            else:
                                if location in set(operate_path):
                                    continue
                                add_path = operate_path + [location]
                                if not N_down_water:
                                    set_of_searched_point.add(location)
                                queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        else:
                            for tuples in list_of_tree_stone_island:
                                if location in tuples[0]:# if this land is another land which have stone or tree or keys.
                                    if location in set(operate_path):
                                        continue
                                    if not have_key:
                                        have_key = tuples[3]
                                    add_path = operate_path + [location]
                                    new_nb_of_stone = tuples[1] + nb_of_stone
                                    if rafting == True:# if we sit on raft to get there.
                                        have_tree = tuples[2]# judge if this island has tree.
                                        rafting = False
                                    else:# if we use stone to get there
                                        if tuples[2]:# if this island has tree.
                                            have_tree = True
                                    for points in tuples[0]:
                                        location_of_this_land.add(points)
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    break
                            # if this island does not have tree or stone or keys.
                            if len(queue) != 0:
                                if queue[0][0][-1] != location:# if we have no operations above,
                                    if rafting == True:# if we use raft to go there.
                                        rafting = False
                                        if location in set(operate_path):
                                            continue
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    else:# we still have stone.
                                        if location in set(operate_path):
                                            continue
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                if rafting == True:# if we use raft to go there.
                                    rafting = False
                                    if location in set(operate_path):
                                        continue
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                else:# we still have stone.
                                    if location in set(operate_path):
                                        continue
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])

                if not self.sit_in_a_raft:
                    if self.map[location[0]][location[1]] in {'~'}:# if in the water
                        New_down_water = True
                        if nb_of_stone > 0:# if have stone, using stone firstly
                            if location in set(operate_path):
                                continue
                            new_stone = nb_of_stone - 1
                            add_path = operate_path + [location]
                            queue.appendleft([add_path, new_stone, have_tree, have_key, rafting, New_down_water])
                        elif nb_of_stone == 0:
                            if have_tree or rafting:# if we don't have stone, using tree.
                                have_tree = False
                                rafting = True
                                add_path = operate_path + [location]
                                set_of_searched_point.add(location)
                                queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, New_down_water])
                    elif self.map[location[0]][location[1]] != '~':# if we land in again.
                        if location == (self.initial_location[0], self.initial_location[1]):# if we found the birth point.
                            return True

                        elif location in location_of_this_land:# if the land is the location of this land.
                            if location in set(operate_path):
                                continue
                            add_path = operate_path + [location]
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        elif self.map[location[0]][location[1]] == '-':
                            if not have_key:# if this path do not have key.
                                continue
                            else:
                                if location in set(operate_path):
                                    continue
                                add_path = operate_path + [location]
                                if not N_down_water:
                                    set_of_searched_point.add(location)
                                queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        else:
                            for tuples in list_of_tree_stone_island:
                                if location in tuples[0]:# if this land is another land which have stone or tree or keys.
                                    if location in set(operate_path):
                                        continue
                                    if not have_key:
                                        have_key = tuples[3]
                                    add_path = operate_path + [location]
                                    new_nb_of_stone = tuples[1] + nb_of_stone
                                    if rafting == True:# if we sit on raft to get there.
                                        have_tree = tuples[2]# judge if this island has tree.
                                        rafting = False
                                    else:# if we use stone to get there
                                        if tuples[2]:# if this island has tree.
                                            have_tree = True
                                    for points in tuples[0]:
                                        location_of_this_land.add(points)
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    break
                            # if this island does not have tree or stone or keys.
                            if len(queue) != 0:
                                if queue[0][0][-1] != location:# if we have no operations above,
                                    if rafting == True:# if we use raft to go there.
                                        rafting = False
                                        if location in set(operate_path):
                                            continue
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    else:# we still have stone.
                                        if location in set(operate_path):
                                            continue
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                if rafting == True:# if we use raft to go there.
                                    rafting = False
                                    if location in set(operate_path):
                                        continue
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                else:# we still have stone.
                                    if location in set(operate_path):
                                        continue
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])

#############################################################################################################

    #### This function is used for the condition that we only have raft. #####
    def search_path_with_raft(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]
            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a'}:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                for location in self.searched_tree[operate_location]:# four possible path.
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T', '-', '~'}):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':
                        out_put_string = self.decode_location_into_string((operate_list + [location], 0))
                        return out_put_string

                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]
            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a'}:
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string
                else:
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string


            # if we already find every path in the land. find if there is a treasure.
            self.catch_treasure()

            # if not, go futher and continue our search.
            # find if there is a tree block our way to resources or unknown area.
            # find a water and search it.
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', 'T', '-'}):
                        continue
                    elif self.map[location[0]][location[1]] == '~':
                        check_water = self.is_target_water(location)
                        if check_water:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))# go down to the water.
                            return out_put_string
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)

            # if there isn't any water, find another obstacle tree, and cut it down.
            self.find_location_of_tree()

            target_tree = self.find_target_tree(set_of_searched_path)
            if target_tree == None:
                return
            else:
                set_of_searched_point = set()
                queue = deque()
                set_of_searched_point.add(self.location)
                queue.appendleft([self.location])
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if self.map[location[0]][location[1]] == '.':
                            continue
                        elif self.map[location[0]][location[1]] in {'*', '-'} or location in set_of_searched_point:
                            continue
                        elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                            if location != target_tree[0]:# if the tree is not the target tree.
                                continue
                            else:
                                if target_tree[1] == 'Possible':
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    return out_put_string
                                else:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                        else:
                            add_list = operate_list + [location]
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)
        
        # if we have found the treasure.
        else:
            # firstly, find a way to home.
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue

                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string

                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        if self.map[location[0]][location[1]] == '~':
                            if self.find_backhome_water(location):# judge which water can take us to our home.
                                add_list = operate_list + [location]
                                out_put_string = self.decode_location_into_string((add_list, 0))
                                return out_put_string
                            else:
                                continue
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)

            # if not, search further.
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', 'T'}):
                        continue
                    elif self.map[location[0]][location[1]] == '~':
                        check_water = self.is_target_water(location)# if there is unsearched water area
                        if check_water:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))# go down to the water.
                            return out_put_string
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)
            




#############################################################################################################

    #### This function is used for the condition that we have raft and key. #####
    def search_path_with_raft_key(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()# add the position of agent into search queue.
            set_of_searched_path.add((self.location[0], self.location[1]))
            operate_list = [(self.location[0], self.location[1])]
            operate_location = operate_list[-1]
            while self.map[operate_location[0]][operate_location[1]] not in {'?', 'o', 'k', 'a', '-'}:
                # As long as we haven't find the edge or we have found all the possible path.
                # continue BFS.
                for location in self.searched_tree[operate_location]:# four possible path.
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T', '~'}):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':
                        out_put_string = self.decode_location_into_string((operate_list + [location], 0))
                        return out_put_string

                    else:
                        add_list = operate_list + [(location[0], location[1])]
                        set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                        queue.appendleft(add_list)
                if len(queue) == 0:
                    break
                operate_list = queue.pop()
                operate_location = operate_list[-1]
            if self.map[operate_location[0]][operate_location[1]] in {'?', 'o', 'k', 'a', '-'}:
                if self.map[operate_list[-1][0]][operate_list[-1][1]] in {'o', 'k', 'a'}:
                    out_put_string = self.decode_location_into_string((operate_list, 0))
                    return out_put_string
                elif self.map[operate_list[-1][0]][operate_list[-1][1]] == '-':
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    out_put_string += 'u'
                    return out_put_string
                else:
                    out_put_string = self.decode_location_into_string((operate_list[: -1], (operate_list[-1][0], operate_list[-1][1])))
                    return out_put_string

            # if we already find every path in the land. find if there is a treasure.
            self.catch_treasure()

            # find a water and search it.
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', 'T'}):
                        continue
                    elif self.map[location[0]][location[1]] == '~':
                        check_water = self.is_target_water(location)# if there is unsearched water area
                        if check_water:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))# go down to the water.
                            return out_put_string
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)


            # if there isn't any water, find an obstacle tree, and cut it down.
            self.find_location_of_tree()

            target_tree = self.find_target_tree(set_of_searched_path)
            if target_tree == None:
                return
            else:
                set_of_searched_point = set()
                queue = deque()
                set_of_searched_point.add(self.location)
                queue.appendleft([self.location])
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if self.map[location[0]][location[1]] == '.':
                            continue
                        elif self.map[location[0]][location[1]] in {'*'} or location in set_of_searched_point:
                            continue
                        elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                            if location != target_tree[0]:# if the tree is not the target tree.
                                continue
                            else:
                                if target_tree[1] == 'Possible':
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    return out_put_string
                                else:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                        else:
                            add_list = operate_list + [location]
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)

        # if we have found the treasure.
        else:
            # firstly, find a way to home.
            self.update_search_tree()
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if location in set_of_searched_path or self.map[location[0]][location[1]] == '.':
                        continue
                    elif self.map[location[0]][location[1]] in {'*', 'T', '-', '~', '?'}:
                        if self.map[location[0]][location[1]] == '~':
                            if self.find_backhome_water(location):# judge which water can take us to our home.
                                add_list = operate_list + [location]
                                out_put_string = self.decode_location_into_string((add_list, 0))
                                return out_put_string
                            else:
                                continue
                        elif self.map[location[0]][location[1]] == '-':
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'u'
                            return out_put_string
                        else:
                            continue
                    elif location == (self.initial_location[0], self.initial_location[1]):
                        add_list = operate_list + [location]
                        out_put_string = self.decode_location_into_string((add_list, 0))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)

            # if not, continue searching the island and try to collect other resource.
            set_of_searched_path = set()
            queue = deque()
            set_of_searched_path.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'.', '*', 'T'}):
                        continue
                    elif self.map[location[0]][location[1]] == '~':
                        check_water = self.is_target_water(location)# if there is unsearched water area
                        if check_water:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))# go down to the water.
                            return out_put_string
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_path.add(location)
                        queue.appendleft(add_list)


#############################################################################################################

    #### This function is used for the condition that we have stone and axe. #####
    # firstly, we go as far as we can (in the land area).
    # if we have already searched all the path in the land, find an obstacle tree and cut it down.
    # if there isn't any tree, we can search the water area with the algorithm of 'search path with stone'.
    def search_path_with_stone_hammer(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.' or location in set_of_searched_point:
                        continue

                    elif self.map[location[0]][location[1]] == '-':
                        continue

                    elif self.map[location[0]][location[1]] in {'*', 'T', '~'}:
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                    elif self.map[location[0]][location[1]] in {'?', 'o', 'k', 'a'}:
                        if self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        elif self.map[location[0]][location[1]] in {'?'}:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            return out_put_string

                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

            # we have already searched all the path in the land, find an obstacle tree and cut it down.
            self.find_location_of_tree()
            target_tree = self.find_target_tree(set_of_searched_point)

            if not self.have_raft:# if we don't have raft.
                if target_tree != None:# if there is a target tree.
                    set_of_searched_point = set()
                    queue = deque()
                    set_of_searched_point.add(self.location)
                    queue.appendleft([self.location])
                    while len(queue) != 0:
                        operate_list = queue.pop()
                        operate_location = operate_list[-1]
                        for location in self.searched_tree[operate_location]:
                            if self.map[location[0]][location[1]] == '.':
                                continue
                            elif self.map[location[0]][location[1]] in {'*'} or location in set_of_searched_point:
                                continue
                            elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                                if location != target_tree[0]:# if the tree is not the target tree.
                                    continue
                                else:
                                    if target_tree[1] == 'Possible':
                                        out_put_string = self.decode_location_into_string((operate_list, location))
                                        return out_put_string
                                    else:
                                        out_put_string = self.decode_location_into_string((operate_list, location))
                                        out_put_string += 'c'
                                        return out_put_string
                            else:
                                add_list = operate_list + [location]
                                set_of_searched_point.add(location)
                                queue.appendleft(add_list)

            # if there isn't any tree in the land or we already have raft, we can search the water area.
            out_put_string = self.search_path_with_stone()
            return out_put_string
            # if there isn't a way, cut a tree which is obstacle to go further.
            if target_tree != None:# if there is a target tree.
                set_of_searched_point = set()
                queue = deque()
                set_of_searched_point.add(self.location)
                queue.appendleft([self.location])
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if self.map[location[0]][location[1]] == '.':
                            continue
                        elif self.map[location[0]][location[1]] in {'*'} or location in set_of_searched_point:
                            continue
                        elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                            if location != target_tree[0]:# if the tree is not the target tree.
                                continue
                            else:
                                if target_tree[1] == 'Possible':
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    return out_put_string
                                else:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                        else:
                            add_list = operate_list + [location]
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)


        # if we have found treasure.
        else:
           # judge if we can go back without using extra stone.
            self.update_search_tree()
            birth_land = self.find_the_initial_land_area()
            number_of_stone = self.have_rock[1]
            for i in range(number_of_stone + 1):
                self.update_search_tree()
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                down_water = False
                set_of_searched_path.add((self.location[0], self.location[1]))
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]

                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] in {'.', '*', 'T', '-', '?'} or (location in set_of_searched_path):
                            continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif location == (self.initial_location[0], self.initial_location[1]):
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])

            # if not, find enough resource as much as possible.
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                down_water = False

                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.':
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            left_stone = i - time_of_cross_water
                            New_down_water = True
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T'}):
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue

                        elif self.map[location[0]][location[1]] == '-':
                            continue

                        elif self.map[location[0]][location[1]] == 'T':
                            if not self.have_raft:# if we haven't have raft.
                                out_put_string = self.decode_location_into_string((operate_path, location))
                                out_put_string += 'cf'
                                return out_put_string


                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            set_of_searched_path.add(location)
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])



#############################################################################################################

    #### This function is used for the condition that we have stone, axe and key. #####
    # the principle is similar to the function above, just add the condition of having key.
    
    def search_path_with_stone_hammer_key(self):
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.' or location in set_of_searched_point:
                        continue

                    elif self.map[location[0]][location[1]] == '-':
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        out_put_string += 'u'
                        return out_put_string

                    elif self.map[location[0]][location[1]] in {'*', 'T', '~'}:
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '$':
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string

                    elif self.map[location[0]][location[1]] in {'?', 'o', 'k', 'a'}:
                        if self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        elif self.map[location[0]][location[1]] in {'?'}:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            return out_put_string

                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

            # we have already searched all the path in the land, find an obstacle tree and cut it down.
            self.find_location_of_tree()
            target_tree = self.find_target_tree(set_of_searched_point)
            if not self.have_raft:
                if target_tree != None:# if there is a target tree.
                    set_of_searched_point = set()
                    queue = deque()
                    set_of_searched_point.add(self.location)
                    queue.appendleft([self.location])
                    while len(queue) != 0:
                        operate_list = queue.pop()
                        operate_location = operate_list[-1]
                        for location in self.searched_tree[operate_location]:
                            if self.map[location[0]][location[1]] == '.':
                                continue
                            elif self.map[location[0]][location[1]] in {'*'} or location in set_of_searched_point:
                                continue
                            elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                                if location != target_tree[0]:# if the tree is not the target tree.
                                    continue
                                else:
                                    if target_tree[1] == 'Possible':
                                        out_put_string = self.decode_location_into_string((operate_list, location))
                                        return out_put_string
                                    else:
                                        out_put_string = self.decode_location_into_string((operate_list, location))
                                        out_put_string += 'c'
                                        return out_put_string
                            else:
                                add_list = operate_list + [location]
                                set_of_searched_point.add(location)
                                queue.appendleft(add_list)

            # if there isn't any tree in the land or we already have a raft, we can search the water area.
            out_put_string = self.search_path_with_stone_key()
            return out_put_string
            # if there isn't any way, cut the tree which is obstacle to go further.
            if target_tree != None:# if there is a target tree.
                set_of_searched_point = set()
                queue = deque()
                set_of_searched_point.add(self.location)
                queue.appendleft([self.location])
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_location = operate_list[-1]
                    for location in self.searched_tree[operate_location]:
                        if self.map[location[0]][location[1]] == '.':
                            continue
                        elif self.map[location[0]][location[1]] in {'*'} or location in set_of_searched_point:
                            continue
                        elif self.map[location[0]][location[1]] == 'T':# check if it is a target tree:
                            if location != target_tree[0]:# if the tree is not the target tree.
                                continue
                            else:
                                if target_tree[1] == 'Possible':
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    return out_put_string
                                else:
                                    out_put_string = self.decode_location_into_string((operate_list, location))
                                    out_put_string += 'c'
                                    return out_put_string
                        else:
                            add_list = operate_list + [location]
                            set_of_searched_point.add(location)
                            queue.appendleft(add_list)


        # if we have found treasure.
        else:
           # judge if we can go back without using extra stone.
            self.update_search_tree()
            birth_land = self.find_the_initial_land_area()
            number_of_stone = self.have_rock[1]
            for i in range(number_of_stone + 1):
                self.update_search_tree()
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                down_water = False
                set_of_searched_path.add((self.location[0], self.location[1]))
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]

                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] in {'.', '*', 'T', '-', '?'} or (location in set_of_searched_path):
                            continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            left_stone = i - time_of_cross_water
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif location == (self.initial_location[0], self.initial_location[1]):
                            add_list = operate_path + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])

            # if not, find enough resource as much as possible.
            for i in range(number_of_stone + 1):
                set_of_searched_path = set()
                queue = deque()# add the position of agent into search queue.
                set_of_searched_path.add((self.location[0], self.location[1]))
                down_water = False
                initial_list = [[(self.location[0], self.location[1])], 0, down_water]
                queue.appendleft(initial_list)
                down_water = False

                while len(queue) != 0:
                    operate_list = queue.pop()
                    time_of_cross_water = operate_list[1]
                    operate_path = operate_list[0]
                    operate_location = operate_path[-1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_location]:# four possible path.
                        if self.map[location[0]][location[1]] == '.':
                            continue

                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            left_stone = i - time_of_cross_water
                            New_down_water = True
                            if left_stone > 0:
                                add_list = operate_path + [(location[0], location[1])]
                                new_time = time_of_cross_water + 1
                                queue.appendleft([add_list, new_time, New_down_water])
                            else:
                                continue

                        elif (location in set_of_searched_path) or (self.map[location[0]][location[1]] in {'*', 'T'}):
                            if self.is_mist_area_around(location):
                                out_put_string = self.decode_location_into_string((operate_path, 0))
                                return out_put_string
                            else:
                                continue

                        elif self.map[location[0]][location[1]] == '-':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            out_put_string += 'u'
                            return out_put_string

                        elif self.map[location[0]][location[1]] == 'T':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            out_put_string += 'cf'
                            return out_put_string


                        elif self.map[location[0]][location[1]] in {'o', 'k', 'a'}:
                            add_list = operate_path + [(location[0], location[1])]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            set_of_searched_path.add(location)
                            return out_put_string

                        elif self.map[location[0]][location[1]] == '?':
                            out_put_string = self.decode_location_into_string((operate_path, location))
                            return out_put_string

                        else:
                            if location in set(operate_path):
                                continue
                            add_list = operate_path + [(location[0], location[1])]
                            if not N_down_water:
                                set_of_searched_path.add(add_list[-1])# add each searched location to the set.
                            queue.appendleft([add_list, time_of_cross_water, N_down_water])


#############################################################################################################

    #### This function is used for the condition that we have stone, axe and raft. #####
    # firstly, we search the land area as far as possible.
    # if we still in the birth land, we just find a path to the sea, to explore the unknown area.
    # once we located in another island, there may be two choice:
    # One is we build a path to our birth island, another is continue search the unknown area.
    # we believe that if the number of stone we have is equal to the needed stone to bulid a path, we build a path
    # to our birth island, and then use the raft to search the unknown area.
    # However, if the number of stone we have is not equal to the needed stone to bulid a path, we search forward.

    def search_path_with_stone_raft(self):
        self.update_search_tree()
        if not self.have_treasure:
            if not self.have_searched_the_sea:
                out_put_string = self.search_path_with_stone_hammer()
                if out_put_string:
                    return out_put_string
            else:
                birth_land = self.find_the_initial_land_area()
                nb_of_stone = self.have_rock[1]
                queue = deque()
                set_of_searched_point = set()
                down_water = False
                queue.appendleft([[self.location], nb_of_stone, down_water])
                set_of_searched_point.add(self.location)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_path = operate_list[0]
                    nb_of_stone = operate_list[1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_path[-1]]:
                        if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*'}:
                            continue
                        elif location in birth_land:
                            if nb_of_stone == 0:
                                out_put_string = self.decode_location_into_string((operate_path, location))
                                return out_put_string
                            else:
                                continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            if nb_of_stone > 0:
                                new_stone = nb_of_stone - 1
                                add_path = operate_path + [location]
                                queue.appendleft([add_path, new_stone, New_down_water])
                            else:
                                continue
                        else:
                            if location in set(operate_path):
                                continue
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            queue.appendleft([operate_path + [location], nb_of_stone, N_down_water])
                # if the number of stone we have is not equal to the needed stone to bulid a path, we search forward.
                out_put_string = self.search_path_with_stone_hammer()
                if out_put_string:
                    return out_put_string
        else:
            out_put_string = self.search_path_with_stone_hammer()
            if out_put_string:
                return out_put_string






#############################################################################################################

    #### This function is used for the condition that we have stone, axe and raft, and key. #####

    def search_path_with_stone_raft_key(self):
        self.update_search_tree()
        if not self.have_treasure:
            if not self.have_searched_the_sea:
                out_put_string = self.search_path_with_stone_hammer()
                if out_put_string:
                    return out_put_string
            else:
                birth_land = self.find_the_initial_land_area()
                nb_of_stone = self.have_rock[1]
                queue = deque()
                set_of_searched_point = set()
                down_water = False
                queue.appendleft([[self.location], nb_of_stone, down_water])
                set_of_searched_point.add(self.location)
                while len(queue) != 0:
                    operate_list = queue.pop()
                    operate_path = operate_list[0]
                    nb_of_stone = operate_list[1]
                    N_down_water = operate_list[2]
                    for location in self.searched_tree[operate_path[-1]]:
                        if location in set_of_searched_point or self.map[location[0]][location[1]] in {'.', '*'}:
                            continue
                        elif location in birth_land:
                            if nb_of_stone == 0:
                                out_put_string = self.decode_location_into_string((operate_path, location))
                                return out_put_string
                            else:
                                continue
                        elif self.map[location[0]][location[1]] == '~':
                            if location in set(operate_path):
                                continue
                            New_down_water = True
                            if nb_of_stone > 0:
                                new_stone = nb_of_stone - 1
                                add_path = operate_path + [location]
                                queue.appendleft([add_path, new_stone, New_down_water])
                            else:
                                continue
                        else:
                            if location in set(operate_path):
                                continue
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            queue.appendleft([operate_path + [location], nb_of_stone, N_down_water])
                    # if the number of stone we have is not equal to the needed stone to bulid a path, we search forward.
                    out_put_string = self.search_path_with_stone_hammer_key()
                    if out_put_string:
                        return out_put_string

        else:
            out_put_string = self.search_path_with_stone_hammer_key()
            if out_put_string:
                return out_put_string

#############################################################################################################

    #### This function is used for find what is in the island. #####
    #  input: one land located in this island nearing the water.
    # output: tuple: (have_tree, have_treasure, have_rock, have_mist, have_key, have_initial_location, 
    #                 set of point in this island, one landing point in this island.)
    
    def what_is_on_the_island(self, point):
        self.update_search_tree()
        have_tree = False
        have_rock = False
        nb_of_rock = 0
        have_treasure = False
        have_mist = False
        have_key = False
        have_initial_location = False

        if self.map[point[0]][point[1]] == 'T':
            have_tree = True
        if self.map[point[0]][point[1]] == 'o':
            have_rock = True
            nb_of_rock += 1
        if self.map[point[0]][point[1]] == '$':
            have_treasure = True
        if self.map[point[0]][point[1]] == 'k':
            have_key = True
        if point == (self.initial_location[0], self.initial_location[1]):
            have_initial_location = True


        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(point)
        queue.appendleft([point])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if self.map[location[0]][location[1]] == '.' or (location in set_of_searched_point):
                    continue
                elif self.map[location[0]][location[1]] in {'*', '~'}:
                    continue

                elif self.map[location[0]][location[1]] in {'>', '<', '^', 'v'}:
                    if self.sit_in_a_raft:
                        continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)
                        continue

                elif self.map[location[0]][location[1]] == 'T':
                    have_tree = True
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
                    continue
                elif self.map[location[0]][location[1]] == 'o':
                    have_rock = True
                    nb_of_rock += 1
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
                    continue
                elif self.map[location[0]][location[1]] == '$':
                    have_treasure = True
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
                    continue

                elif self.map[location[0]][location[1]] == 'k':
                    have_key = True
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
                    continue

                elif self.map[location[0]][location[1]] == '?':
                    have_mist = True
                    set_of_searched_point.add(location)
                    continue
                elif location == (self.initial_location[0], self.initial_location[1]):
                    have_initial_location = True
                    set_of_searched_point.add(location)
                    add_list = operate_list + [location]
                    queue.appendleft(add_list)
                    continue

                else:
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
        return (have_tree, have_treasure, (have_rock, nb_of_rock), have_mist, have_key, have_initial_location, set_of_searched_point, point)

#############################################################################################################

    #### This function is used for making a decision of which island should we land in. #####
    #  input: the list of information of island.
    # output: the location of choiced island.
    
    def make_landing_decision(self, compare_list):
        if not self.have_treasure:
            if not self.have_key:# if we haven't found a key, find a key first.
                for _tuple in compare_list:
                    if _tuple[0] and _tuple[1] and _tuple[4]:# if the island has treasure and trees and keys, land in.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[1] and _tuple[2][0] and _tuple[4]:# if the island has treasure and stones and keys, check if we can back home.
                        if self.back_home_stone_island(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0] and _tuple[4]:# if the island has tree and stones and keys, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3] and _tuple[1] and _tuple[4]:# if the island has treasure and mist and keys, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0] and _tuple[4]:# if the island has tree and mist and keys, we can land in.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2] and _tuple[3] and _tuple[4]:# if the island has stone and mist and keys, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[4]:# if the island has tree and keys, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2][0] and _tuple[4]:# if the island has stone and keys, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3] and _tuple[4]:# if the island has mist and keys, we can land in and check.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[1]:# if the island has treasure and trees, land in.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[1] and _tuple[2][0]:# if the island has treasure and stones, check if we can back home.
                        if self.back_home_stone_island(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0]:# if the island has tree and stones, check if we can go further.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3] and _tuple[1]:# if the island has treasure and mist, we can land in and check.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0]:# if the island has tree and mist, we can land in.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2][0] and _tuple[3]:# if the island has stone and mist, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0]:# if the island has tree, check if we can go further,
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2][0]:# if the island has stone, check if we can go further,
                        #print((self.land_lead_to_target(_tuple[-1]), _tuple[-1]))
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3]:# if the island has mist, we can land in and check.
                        return _tuple[-1]

                return max(compare_list, key = lambda x: x[2][1])[-1]
            
            else:
                for _tuple in compare_list:
                    if _tuple[0] and _tuple[1]:# if the island has treasure and trees, land in.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[1] and _tuple[2][0]:# if the island has treasure and stones, check if we can back home.
                        if self.back_home_stone_island(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0]:# if the island has tree and stones, check if we can go further.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3] and _tuple[1]:# if the island has treasure and mist, we can land in and check.
                        return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0] and _tuple[2][0]:# if the island has tree and mist, we can land in.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2][0] and _tuple[3]:# if the island has stone and mist, we can land in and check.
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[0]:# if the island has tree, check if we can go further,
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[2][0]:# if the island has stone, check if we can go further,
                        if self.land_lead_to_target(_tuple[-1]):
                            return _tuple[-1]

                for _tuple in compare_list:
                    if _tuple[3]:# if the island has mist, we can land in and check.
                        return _tuple[-1]

                return max(compare_list, key = lambda x: x[2][1])[-1]

#############################################################################################################

    #### This function is used for making a decision of which island can lead us to unknown area or finding treasure. #####

    def land_lead_to_target(self, point):
        list_of_stone_tree_land = self.find_all_stone_island()# all island area which can be seen like water.
        this_water = self.find_current_water_area()
        set_of_searched_land = set()
        have_tree = False
        rafting = False
        have_key = self.have_key
        nb_of_stone = 0
        down_water = False
        for _tuple in list_of_stone_tree_land:
            if point in _tuple[0]:
                have_tree = _tuple[2]
                nb_of_stone = _tuple[1]
                if not have_key:
                    have_key = _tuple[3]
                set_of_searched_land = _tuple[0]
                break
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(point)
        set_of_searched_land.add(point)
        queue.appendleft([[point], nb_of_stone, have_tree, have_key, rafting, down_water])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_path = operate_list[0]
            have_tree = operate_list[2]
            have_key = operate_list[3]
            rafting = operate_list[4]
            N_down_water = operate_list[5]
            nb_of_stone = operate_list[1]
            operate_location = operate_path[-1]
            for location in self.searched_tree[operate_location]:
                if self.map[location[0]][location[1]] in {'.', '*'} or location in set_of_searched_point:
                    continue

                elif self.map[location[0]][location[1]] == '?':
                    return True

                elif self.map[location[0]][location[1]] == '$':
                    if self.back_home_stone_island(location):
                        return True

                if self.sit_in_a_raft:
                    if self.map[location[0]][location[1]] in {'~', '<', '>', '^', 'v'}:
                        # using stone at first.
                        New_down_water = True
                        if location in this_water or location in set(operate_path):
                            continue
                        if nb_of_stone:
                            if location in set(operate_path):
                                continue
                            new_nb_of_stone = nb_of_stone - 1
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, New_down_water])
                        elif have_tree:
                            have_tree = False
                            rafting = True
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, New_down_water])
                        else:
                            continue

                    elif self.map[location[0]][location[1]] != '~':
                        if location in set(operate_path):
                            continue
                        elif location in set_of_searched_land:# if we already land in this land.
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        elif self.map[location[0]][location[1]] == '-':
                            if have_key:
                                if not N_down_water:
                                    set_of_searched_point.add(location)
                                add_list = operate_path + [location]
                                queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                continue

                        else:# if we land in a new land.
                            for _tuple in list_of_stone_tree_land:# check if this land has tree or stone.
                                if location in _tuple[0]:# if it have stone, key or trees.
                                    if rafting == True:# if we don't have stone.
                                        if not have_key:
                                            have_key = _tuple[3]
                                        have_tree = _tuple[2]
                                        rafting = False
                                        new_nb_of_stone = _tuple[1]
                                        for points in _tuple[0]:
                                            set_of_searched_land.add(points)
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        add_list = operate_path + [location]
                                        queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                        break
                                    else:# if we have stone
                                        if not have_key:
                                            have_key = _tuple[3]
                                        new_nb_of_stone = _tuple[1] + nb_of_stone
                                        for points in _tuple[0]:
                                            set_of_searched_land.add(points)
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        add_list = operate_path + [location]
                                        queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                        break
                            # if this land do not have tree or stone or keys
                            if len(queue) != 0:
                                if queue[0][0][-1] != location:# if we have no operations above,
                                    if rafting == True:# if we use raft to go there.
                                        rafting = False
                                        have_tree = False
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    else:# we still have stone.
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                if rafting == True:# if we use raft to go there.
                                    rafting = False
                                    have_tree = False
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                else:# we still have stone.
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])

                
                if not self.sit_in_a_raft:
                    if self.map[location[0]][location[1]] in {'~'}:
                        # using stone at first.
                        New_down_water = True
                        if location in this_water or location in set(operate_path):
                            continue
                        if nb_of_stone:
                            if location in set(operate_path):
                                continue
                            new_nb_of_stone = nb_of_stone - 1
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, New_down_water])
                        elif have_tree:
                            have_tree = False
                            rafting = True
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, New_down_water])
                        else:
                            continue

                    elif self.map[location[0]][location[1]] != '~':
                        if location in set(operate_path):
                            continue
                        elif location in set_of_searched_land:# if we already land in this land.
                            if not N_down_water:
                                set_of_searched_point.add(location)
                            add_list = operate_path + [location]
                            queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                        elif self.map[location[0]][location[1]] == '-':
                            if have_key:
                                if not N_down_water:
                                    set_of_searched_point.add(location)
                                add_list = operate_path + [location]
                                queue.appendleft([add_list, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                continue

                        else:# if we land in a new land.
                            for _tuple in list_of_stone_tree_land:# check if this land has tree or stone.
                                if location in _tuple[0]:# if it have stone, key or trees.
                                    if rafting == True:# if we don't have stone.
                                        if not have_key:
                                            have_key = _tuple[3]
                                        have_tree = _tuple[2]
                                        rafting = False
                                        new_nb_of_stone = _tuple[1]
                                        for points in _tuple[0]:
                                            set_of_searched_land.add(points)
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        add_list = operate_path + [location]
                                        queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                        break
                                    else:# if we have stone
                                        if not have_key:
                                            have_key = _tuple[3]
                                        new_nb_of_stone = _tuple[1] + nb_of_stone
                                        for points in _tuple[0]:
                                            set_of_searched_land.add(points)
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        add_list = operate_path + [location]
                                        queue.appendleft([add_list, new_nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                        break
                            # if this land do not have tree or stone or keys
                            if len(queue) != 0:
                                if queue[0][0][-1] != location:# if we have no operations above,
                                    if rafting == True:# if we use raft to go there.
                                        rafting = False
                                        have_tree = False
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                    else:# we still have stone.
                                        add_path = operate_path + [location]
                                        if not N_down_water:
                                            set_of_searched_point.add(location)
                                        queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                            else:
                                if rafting == True:# if we use raft to go there.
                                    rafting = False
                                    have_tree = False
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])
                                else:# we still have stone.
                                    add_path = operate_path + [location]
                                    if not N_down_water:
                                        set_of_searched_point.add(location)
                                    queue.appendleft([add_path, nb_of_stone, have_tree, have_key, rafting, N_down_water])



#############################################################################################################

    #### This function is used for finding the current water area. #####

    def find_current_water_area(self):
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(self.location)
        queue.appendleft([self.location])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if self.map[location[0]][location[1]] != '~' or location in set_of_searched_point:
                    continue
                else:
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)
        return set_of_searched_point

#############################################################################################################
    
    # check if this water is the target water to find a treasure or mist.
    def is_target_water(self, point):
        set_of_this_land = self.find_this_island()
        set_of_searched_point = set()
        queue = deque()
        set_of_searched_point.add(point)
        queue.appendleft([point])
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if self.map[location[0]][location[1]] in {'.', '*'} or location in set_of_searched_point:
                    continue
                elif location in set_of_this_land:
                    continue
                elif self.map[location[0]][location[1]] == '?':
                    return True
                elif self.map[location[0]][location[1]] in {'<', '>', '^', 'v'}:
                    continue
                elif self.map[location[0]][location[1]] == '~':
                    add_list = operate_list + [location]
                    queue.appendleft(add_list)
                    set_of_searched_point.add(location)
                elif self.map[location[0]][location[1]] != '~':
                    if self.land_lead_to_target(location):
                        return True






#############################################################################################################

    #### This function is used for the condition that we are sitting in a raft. #####

    def search_path_in_the_sea(self):
        # if we haven't get the treasure.
        if not self.have_treasure:
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            # search the area of water as much as possible.
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.':
                        continue

                    elif self.map[location[0]][location[1]] in {'*', ' ', 'o', 'k', '$', 'T', 'a'} or (location in set_of_searched_point):
                        if self.is_mist_area_around(location):
                            out_put_string = self.decode_location_into_string((operate_list, 0))
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '?':
                        out_put_string = self.decode_location_into_string((operate_list, location))
                        return out_put_string
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

            # if we have searched all the water area, decide a land to land in.
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            compare_list = []
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.' or (location in set_of_searched_point):
                        continue

                    elif self.map[location[0]][location[1]] in {'*'}:
                        continue

                    elif self.map[location[0]][location[1]] in {' ', 'o', 'k', '$', 'a', 'T'}:
                        compare_list.append(self.what_is_on_the_island(location))
                        for points in compare_list[-1][-2]:
                            set_of_searched_point.add(points)
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

            # after we finish our search in the sea, we may find an island to land in.

            landing_point = self.make_landing_decision(compare_list)# choose a land to land in.
            # search a way to landing_point
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] == '.' or (location in set_of_searched_point):
                        continue

                    elif self.map[location[0]][location[1]] in {'*'}:
                        continue

                    elif self.map[location[0]][location[1]] == 'T':
                        if location == landing_point:
                            current_water_area = self.find_current_water_area()
                            landing_point = self.find_right_landing_area(location, current_water_area)
                            if landing_point:
                                out_put_string = self.navigate_to_landing_point(landing_point[1], landing_point[0])
                                return out_put_string
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'cf'
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] == '-':
                        if location == landing_point:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'uf'
                            return out_put_string
                        else:
                            continue

                    elif self.map[location[0]][location[1]] in {' ', 'o', 'k', '$', 'a'}:
                        if location == landing_point:
                            out_put_string = self.decode_location_into_string((operate_list, location))
                            out_put_string += 'f'
                            return out_put_string
                        else:
                            continue
                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)
        
        # if we have found treasure, find an land which can go home.
        else:
            self.update_search_tree()
            set_of_searched_point = set()
            queue = deque()
            set_of_searched_point.add(self.location)
            queue.appendleft([self.location])
            # search the area of water as much as possible.
            while len(queue) != 0:
                operate_list = queue.pop()
                operate_location = operate_list[-1]
                for location in self.searched_tree[operate_location]:
                    if self.map[location[0]][location[1]] in {'.', '*'} or location in set_of_searched_point:
                        continue

                    elif self.map[location[0]][location[1]] != '~':
                        if self.back_home_stone_island(location) == True:
                            if self.map[location[0]][location[1]] == 'T':
                                current_water_area = self.find_current_water_area()
                                landing_point = self.find_right_landing_area(location, current_water_area)
                                if landing_point:
                                    out_put_string = self.navigate_to_landing_point(landing_point[1], landing_point[0])
                                    return out_put_string
                                out_put_string = self.decode_location_into_string((operate_list, location))
                                out_put_string += 'cf'
                                return out_put_string
                            elif self.map[location[0]][location[1]] == '-':
                                current_water_area = self.find_current_water_area()
                                landing_point = self.find_right_landing_area(location, current_water_area)
                                if landing_point:
                                    out_put_string = self.navigate_to_landing_point(landing_point[1], landing_point[0])
                                    return out_put_string
                                out_put_string = self.decode_location_into_string((operate_list, location))
                                out_put_string += 'uf'
                                return out_put_string
                            add_list = operate_list + [location]
                            out_put_string = self.decode_location_into_string((add_list, 0))
                            return out_put_string
                        else:
                            continue

                    else:
                        add_list = operate_list + [location]
                        set_of_searched_point.add(location)
                        queue.appendleft(add_list)

#############################################################################################################

    # find a landing point which is not a tree.
    def find_right_landing_area(self, point, set_of_sea):
        result = self._find_right_landing_area(point, set_of_sea, None)
        if result:
            return result

    def _find_right_landing_area(self, point, set_of_sea, last_point):
        if self.map[point[0]][point[1]] in {'k', ' ', 'o', 'a'}:
            for neighbour in self.neighbour_of_point(point):
                if neighbour in set_of_sea:
                    return (point, neighbour)
            return None

        elif self.map[point[0]][point[1]] == '-':
            if not self.have_key:# if we don't have key.
                for location in self.neighbour_of_point(point):
                    if location == last_point:
                        continue
                    result = self._find_right_landing_area(location, set_of_sea, point)
                    if not result:
                        continue
                    else:
                        return result
            for neighbour in self.neighbour_of_point(point):
                if neighbour in set_of_sea:
                    return (point, neighbour)
            return None

        elif self.map[point[0]][point[1]] in {'.', '~', '*'}:
            return None

        else:
            for location in self.neighbour_of_point(point):
                if location == last_point:
                    continue
                result = self._find_right_landing_area(location, set_of_sea, point)
                if not result:
                    continue
                else:
                    return result

    def navigate_to_landing_point(self, point_a, point_b):
        queue = deque()
        set_of_searched_point = set()
        queue.appendleft([self.location])
        set_of_searched_point.add(self.location)
        while len(queue) != 0:
            operate_list = queue.pop()
            operate_location = operate_list[-1]
            for location in self.searched_tree[operate_location]:
                if location in set_of_searched_point or self.map[location[0]][location[1]] != '~':
                    continue
                elif location == point_a:
                    add_list = operate_list + [location]
                    out_put_string = self.decode_location_into_string((add_list, point_b))
                    if self.map[point_b[0]][point_b[1]] == '-':
                        out_put_string += 'uf'
                        return out_put_string
                    else:
                        out_put_string += 'f'
                        return out_put_string
                else:
                    add_list = operate_list + [location]
                    set_of_searched_point.add(location)
                    queue.appendleft(add_list)


#############################################################################################################

    def print_memerised_map(self):# print the memerised map
        for i in range(len(self.map)):
            out_put_str = ''
            for j in range(len(self.map[0])):
                out_put_str += self.map[i][j]
            print(out_put_str)

    def get_action(self):

        ## REPLACE THIS WITH AI CODE TO CHOOSE ACTION ##

        # input loop to take input from user (only returns if this is valid)
        while 1:
            #if we haven't find any tools, we use the function: search_path_no_tools().
            if not self.have_rock[0] and not self.have_raft and not self.have_hammer and not self.have_key\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_no_tools()
                if commond_string != None:
                    return commond_string


            # if we only have key, we use the function: search_path_have_key().
            if not self.have_rock[0] and not self.have_raft and not self.have_hammer and self.have_key\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_have_key()
                if commond_string != None:
                    return commond_string


            # if we only have axe, we use the function: search_path_with_hammer().
            if self.have_hammer and not self.have_rock[0] and not self.have_raft and not self.have_key\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_hammer()
                if commond_string != None:
                    return commond_string

            # if we only have stone, we use the function: search_path_with_stone().
            if self.have_rock[0] and not self.have_raft and not self.have_key and not self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone()
                if commond_string != None:
                    return commond_string

            # if we have stone and key, we use the function: search_path_with_stone_key()
            if self.have_rock[0] and self.have_key and not self.have_raft and not self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone_key()
                if commond_string != None:
                    return commond_string

            # if we have axe and key, we use the function: search_path_with_hammer_key()
            if not self.have_rock[0] and self.have_key and not self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_hammer_key()
                if commond_string != None:
                    return commond_string

            # if we only have raft, we use the function: search_path_with_raft()
            if not self.have_rock[0] and not self.have_key and self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_raft()
                if commond_string != None:
                    return commond_string

            # if we have raft and key, we use the function: search_path_with_raft_key()
            if not self.have_rock[0] and self.have_key and self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_raft_key()
                if commond_string != None:
                    return commond_string

            # if we have stone and axe, we use the function: search_path_with_stone_hammer()
            if self.have_rock[0] and not self.have_key and not self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone_hammer()
                if commond_string != None:
                    return commond_string

            # if we have stone, axe and key, we use the function: search_path_with_stone_hammer_key()
            if self.have_rock[0] and self.have_key and not self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone_hammer_key()
                if commond_string != None:
                    return commond_string

            # if we have stone, raft and key, we use the function: search_path_with_stone_raft_key()
            if self.have_rock[0] and self.have_key and self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone_raft_key()
                if commond_string != None:
                    return commond_string

            # if we have stone and raft, we use the function: search_path_with_stone_raft_key()
            if self.have_rock[0] and not self.have_key and self.have_raft and self.have_hammer\
                    and not self.sit_in_a_raft:
                commond_string = self.search_path_with_stone_raft()
                if commond_string != None:
                    return commond_string

            # if we already sit in a raft, we use the function: search_path_in_the_sea()
            if self.sit_in_a_raft:
                commond_string = self.search_path_in_the_sea()
                if commond_string != None:
                    return commond_string


            # if the AI has no idea.
            inp = input("Enter Action(s): ")
            inp.strip()
            final_string = ''
            for char in inp:
                if char in ['f','l','r','c','u','b','F','L','R','C','U','B']:
                    final_string += char
                    if final_string:
                        return final_string[0]# function to take get action from AI or user


    # helper function to print the grid
def print_grid(view):
    print('+-----+')
    for ln in view:
        print("|"+str(ln[0])+str(ln[1])+str(ln[2])+str(ln[3])+str(ln[4])+"|")
    print('+-----+')

if __name__ == "__main__":

    # checks for correct amount of arguments 
    if len(sys.argv) != 3:
        print("Usage Python3 "+sys.argv[0]+" -p port \n")
        sys.exit(1)

    port = int(sys.argv[2])

    # checking for valid port number
    if not 1025 <= port <= 65535:
        print('Incorrect port number')
        sys.exit()

    # creates TCP socket
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
         # tries to connect to host
         # requires host is running before agent
         sock.connect(('localhost',port))
    except (ConnectionRefusedError):
         print('Connection refused, check host is running')
         sys.exit()

    # navigates through grid with input stream of data
    agent = Agent()
    action_str = 's'
    commond_string = ''

    i=0
    j=0
    while 1:
        data=sock.recv(100).decode('utf-8')
        if not data:
            exit()
        for ch in data:
            if (i==2 and j==2):
                view[i][j] = '^'
                view[i][j+1] = ch
                j+=1 
            else:
                view[i][j] = ch
            j+=1
            if j>4:
                j=0
                i=(i+1)%5
        if j==0 and i==0:
            #print_grid(view) # COMMENT THIS OUT ON SUBMISSION
            print()# distinguish each map.
            if action_str == 's':
                agent.generate_initial_map(view)
                agent.print_memerised_map()
                #time.sleep(3)

            if action_str[-1] in {'f', 'F', 'U', 'u', 'c', 'C', 'l', 'L', 'r', 'R'}:
                useful_information = view[0]
                something_before = last_view[1][2]# something in front of the agent
                something_after = view[3][2]
                agent.expand_map(action, useful_information, something_before, something_after)
                agent.print_memerised_map()
            if commond_string == '':
                commond_string = agent.get_action()
                action = commond_string[0]
                commond_string = commond_string[1: ]
            else:
                action = commond_string[0]
                commond_string = commond_string[1: ]
            #print(agent.have_rock)
            time.sleep(0.02) #sleeping for a while for observation.
            last_view = deepcopy(view)# keep the last view in saving

            action_str += action
            sock.send(action.encode('utf-8'))

    sock.close()
