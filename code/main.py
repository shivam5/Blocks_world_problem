import sys
import copy
import re
import heapq
import random
import itertools

class Stack:
    "A container with a last-in-first-out (LIFO) queuing policy."
    def __init__(self):
        self.list = []

    def push(self,item):
        "Push 'item' onto the stack"
        self.list.append(item)

    def pop(self):
        "Pop the most recently pushed item from the stack"
        return self.list.pop()

    def isEmpty(self):
        "Returns True if the stack is empty"
        return len(self.list) == 0

    def printout(self):
        print "STACK"
        for i in self.list:
            print i
        print "\n\n"


class Queue:
    "A container with a first-in-first-out (FIFO) queuing policy."
    def __init__(self):
        self.list = []

    def push(self,item):
        "Enqueue the 'item' into the queue"
        self.list.insert(0,item)

    def pop(self):
        """
          Dequeue the earliest enqueued item still in the queue. This
          operation removes the item from the queue.
        """
        return self.list.pop()

    def isEmpty(self):
        "Returns True if the queue is empty"
        return len(self.list) == 0

class PriorityQueue:
    """
      Implements a priority queue data structure. Each inserted item
      has a priority associated with it and the client is usually interested
      in quick retrieval of the lowest-priority item in the queue. This
      data structure allows O(1) access to the lowest-priority item.
    """
    def  __init__(self):
        self.heap = []
        self.count = 0

    def push(self, item, priority):
        entry = (priority, self.count, item)
        heapq.heappush(self.heap, entry)
        self.count += 1

    def pop(self):
        (_, _, item) = heapq.heappop(self.heap)
        return item

    def isEmpty(self):
        return len(self.heap) == 0

    def update(self, item, priority):
        # If item already in priority queue with higher priority, update its priority and rebuild the heap.
        # If item already in priority queue with equal or lower priority, do nothing.
        # If item not in priority queue, do the same thing as self.push.
        for index, (p, c, i) in enumerate(self.heap):
            if i == item:
                if p <= priority:
                    break
                del self.heap[index]
                self.heap.append((priority, c, item))
                heapq.heapify(self.heap)
                break
        else:
            self.push(item, priority)


class problem():
    """
    This is the problem desciption.
    """

    def __init__(self):

        fin = open(sys.argv[1] ,"r")

        self.N = int (fin.readline().strip())
        self.planner = fin.readline().strip()
        third_line = fin.readline().strip()
        self.initial = fin.readline().strip()
        fifth_line = fin.readline().strip()
        self.goal = fin.readline().strip()

        self.initial = self.initial.split(") (");
        self.goal = self.goal.split(") (");

        self.initial[0] = self.initial[0].replace("(", "")
        self.initial[len(self.initial)-1] = self.initial[len(self.initial)-1].replace(")", "")

        self.goal[0] = self.goal[0].replace("(", "")
        self.goal[len(self.goal)-1] = self.goal[len(self.goal)-1].replace(")", "")

        self.no_proposition = (self.N*self.N) + (3*self.N) + 1


        self.goalState = [0] * self.no_proposition

        #Used in goal stack planning
        self.action=""

        for word in self.goal:
            matchObj = re.match( r'on (\d*) (\d*)', word, re.M|re.I)
            if matchObj:
                blocka = int(matchObj.group(1))
                blockb = int(matchObj.group(2))
                blocka = blocka-1
                blockb = blockb-1
                self.goalState[blocka*self.N+blockb] = 1
                continue

            matchObj = re.match( r'ontable (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                self.goalState[(self.N*self.N)+block-1] = 1
                continue

            matchObj = re.match( r'clear (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                self.goalState[(self.N*self.N)+self.N+block-1] = 1
                continue

            matchObj = re.match( r'hold (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                self.goalState[(self.N*self.N)+(2*self.N)+block-1] = 1
                continue

            matchObj = re.match( r'empty', word, re.M|re.I)
            if matchObj:
                self.goalState[(self.N*self.N)+(3*self.N)] = 1
                continue

        self.goalState = tuple(self.goalState)


    def getGoalState(self):
        return self.goalState

    def getStartState(self):
        """
        Returns the start state.
        """
        initialState = [0] * self.no_proposition

        for word in self.initial:
            matchObj = re.match( r'on (\d*) (\d*)', word, re.M|re.I)
            if matchObj:
                blocka = int(matchObj.group(1))
                blockb = int(matchObj.group(2))
                blocka = blocka-1
                blockb = blockb-1
                initialState[blocka*self.N+blockb] = 1
                continue

            matchObj = re.match( r'ontable (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                initialState[(self.N*self.N)+block-1] = 1
                continue

            matchObj = re.match( r'clear (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                initialState[(self.N*self.N)+self.N+block-1] = 1
                continue

            matchObj = re.match( r'hold (\d*)', word, re.M|re.I)
            if matchObj:
                block = int(matchObj.group(1))
                initialState[(self.N*self.N)+(2*self.N)+block-1] = 1
                continue

            matchObj = re.match( r'empty', word, re.M|re.I)
            if matchObj:
                initialState[(self.N*self.N)+(3*self.N)] = 1
                continue

        return tuple(initialState)


    # Heuristic for the problem. It counts the proposition yet to be satisfied, 
    # or the proposition which are true, but shouldn't be in goal state.
    # Multiplies the proposition with relevant factors, and calculates the final heuristic value
    def checkingoal (self, state):
        x=0
        for i in range(0, self.N*self.N+self.N):
            if self.goalState[i]==1 and state[i]==0:
                x=x+2
            elif self.goalState[i]==0 and state[i]==1:
                x=x+2

        for i in range(self.N*self.N+self.N,self.no_proposition):
            if self.goalState[i]==1 and state[i]==0:
                x=x+1   
            elif self.goalState[i]==0 and state[i]==1:
                x=x+1
        return x


    def isGoalState(self, state):
        """
        Returns whether this search state is a goal state of the problem.
        """
        return state == self.goalState
        

    # For goal stack planning
   	# Function to get relevant action (pick), if the add list contains goal.
   	# There is proper book-keeping and checks, to ensure no redundacy or extra computation
    def getA(self, goal, S, randomorder, currentState, bookkeep, block=-1):
        flag = 0

        if block != -1:
            del randomorder
            randomorder = []
            randomorder.append(block)

        for block in randomorder:
            if ((self.N)*(self.N)+(2*(self.N))+block-1)==goal :
                flag = 1
                action = "pick "+str(block)
                blockx = block
                if tuple(currentState) in bookkeep:
                    l = bookkeep[tuple(currentState)]

                    if isinstance(l[0], int):
                        if goal == l[0] and action == l[1]:
                            flag=0
                            break
                    else:
                        for x in l:
                            if goal == x[0] and action == x[1]:
                                flag=0
                                break
                else:
                    break

        if flag==1:
            self.action = action
            S.push(self.action)
            S.push((((self.N)*(self.N)+blockx-1), ((self.N)*(self.N)+(self.N)+blockx-1), ((self.N)*(self.N))+(3*(self.N)) ))
            S.push(((self.N)*(self.N))+(3*(self.N)))
            S.push(((self.N)*(self.N)+(self.N)+blockx-1))
            S.push(((self.N)*(self.N)+blockx-1))
            return True

        return False


    # For goal stack planning
   	# Function to get relevant action (release), if the add list contains goal.
   	# There is proper book-keeping and checks, to ensure no redundacy or extra computation
    def getB(self, goal, S, randomorder, currentState, bookkeep, block=-1):
        flag = 0

        if block != -1:
            del randomorder
            randomorder = []
            randomorder.append(block)

        for block in randomorder:
            if  (self.N)*(self.N)+(self.N)+block-1==goal or ((self.N)*(self.N)+(3*(self.N)))==goal or ((self.N)*(self.N)+block-1)==goal:
                flag = 1
                action = "release "+str(block)
                blockx = block
                if tuple(currentState) in bookkeep:
                    l = bookkeep[tuple(currentState)]
                    if isinstance(l[0], int):
                        if goal == l[0] and action == l[1]:
                            flag=0
                            break
                    else:
                        for x in l:
                            if goal == x[0] and action == x[1]:
                                flag=0
                                break
                else:
                    break
        
        if flag == 1:
            self.action = action
            S.push(self.action)
            S.push((self.N)*(self.N)+(2*(self.N))+blockx-1)
            return True


        return False


    # For goal stack planning
   	# Function to get relevant action (unstack), if the add list contains goal.
   	# There is proper book-keeping and checks, to ensure no redundacy or extra computation
    def getC(self, goal, S, randomorder, currentState, bookkeep, blocka=-1, blockb=-1):
        flag = 0

        randomordera = copy.deepcopy(randomorder)
        randomorderb = copy.deepcopy(randomorder)

        if blocka != -1:
            del randomordera
            randomordera = []
            randomordera.append(blocka)
        if blockb != -1:
            del randomorderb
            randomorderb = []
            randomorderb.append(blockb)


        for blocka in randomordera:
            for blockb in randomorderb:
                if (blocka == blockb):
                    continue
                if  (self.N)*(self.N)+(2*(self.N))+blocka-1==goal or ((self.N)*(self.N)+(self.N)+blockb-1)==goal :
                    flag = 1
                    action = "unstack "+str(blocka)+" "+str(blockb)
                    blockx = blocka
                    blocky = blockb
                    if tuple(currentState) in bookkeep:
                        l = bookkeep[tuple(currentState)]
                        # print "l3 = ", l
                        if isinstance(l[0], int):
                            if goal == l[0] and action == l[1]:
                                flag=0
                        else:
                            for x in l:
                                if goal == x[0] and action == x[1]:
                                    flag=0
                        if flag == 1:
                            self.action = action
                            S.push(self.action)
                            S.push((((blockx-1)*(self.N)+(blocky-1)), ((self.N)*(self.N)+(self.N)+blockx-1), (((self.N)*(self.N))+(3*(self.N)))))
                            S.push( (self.N)*(self.N)+(self.N)+blockx-1 )
                            S.push( ((self.N)*(self.N))+(3*(self.N)) )
                            S.push( (blockx-1)*(self.N)+(blocky-1) )
                            return True

                    else:
                        self.action = action
                        S.push("unstack "+str(blockx)+" "+str(blocky))
                        S.push((((blockx-1)*(self.N)+(blocky-1)), ((self.N)*(self.N)+(self.N)+blockx-1), (((self.N)*(self.N))+(3*(self.N)))))
                        S.push( (self.N)*(self.N)+(self.N)+blockx-1 )
                        S.push( ((self.N)*(self.N))+(3*(self.N)) )
                        S.push( (blockx-1)*(self.N)+(blocky-1) )
                        return True

        if flag == 1 :
            self.action = action
            S.push(self.action)
            S.push((((blockx-1)*(self.N)+(blocky-1)), ((self.N)*(self.N)+(self.N)+blockx-1), (((self.N)*(self.N))+(3*(self.N)))))
            S.push( (self.N)*(self.N)+(self.N)+blockx-1 )
            S.push( ((self.N)*(self.N))+(3*(self.N)) )
            S.push( (blockx-1)*(self.N)+(blocky-1) )
            return True


        return False


    # For goal stack planning
   	# Function to get relevant action (stack), if the add list contains goal.
   	# There is proper book-keeping and checks, to ensure no redundacy or extra computation
    def getD(self, goal, S, randomorder, currentState, bookkeep, blocka=-1, blockb=-1):

        randomordera = copy.deepcopy(randomorder)
        randomorderb = copy.deepcopy(randomorder)

        if blocka != -1:
            del randomordera
            randomordera = []
            randomordera.append(blocka)
        if blockb != -1:
            del randomorderb
            randomorderb = []
            randomorderb.append(blockb)

        flag = 0
        for blocka in randomorder:
            for blockb in randomorder:
                if (blocka == blockb):
                    continue
                if  (blocka-1)*(self.N)+(blockb-1)==goal or ((self.N)*(self.N)+(3*(self.N)))==goal or ((self.N)*(self.N)+(self.N)+blocka-1)==goal :
                    flag = 1
                    action = "stack "+str(blocka)+" "+str(blockb)
                    blockx = blocka
                    blocky = blockb
                    if tuple(currentState) in bookkeep:
                        l = bookkeep[tuple(currentState)]
                        # print "l4 = ", l
                        if isinstance(l[0], int):
                            if goal == l[0] and action == l[1]:
                                flag=0
                        else:
                            for x in l:
                                if goal == x[0] and action == x[1]:
                                    flag=0
                        if flag == 1:
                            self.action = action
                            S.push(self.action)
                            S.push( ( ((self.N)*(self.N)+(self.N)+blocky-1 ),  (((self.N)*(self.N))+(2*(self.N))+blockx-1 )))
                            S.push( (self.N)*(self.N)+(self.N)+blocky-1 )
                            S.push( ((self.N)*(self.N))+(2*(self.N))+blockx-1 )
                            return True

                    else:
                        self.action = action
                        S.push("stack "+str(blockx)+" "+str(blocky))
                        S.push((( (self.N)*(self.N)+(self.N)+blocky-1 ),  ( ((self.N)*(self.N))+(2*(self.N))+blockx-1 )))
                        S.push( (self.N)*(self.N)+(self.N)+blocky-1 )
                        S.push( ((self.N)*(self.N))+(2*(self.N))+blockx-1 )
                        return True




        if flag == 1 :
            self.action = action
            S.push(self.action)
            S.push( (((self.N)*(self.N)+(self.N)+blocky-1), ((self.N)*(self.N)+(2*(self.N))+blockx-1)) )
            S.push( (self.N)*(self.N)+(self.N)+blocky-1 )
            S.push((self.N)*(self.N)+(2*(self.N))+blockx-1)
            return True

        return False


    # Relevant action selector for goal stack planning
    def getRelevantState(self, goal, S, currentState, bookkeep):
        randomorder = range(1, self.N + 1)

        # The actions are selected intelligently based on the preconditions and the current state.
        # The high level details are given in the comments.

        # if ontable block:
        #     release block
        if goal >= self.N*self.N and goal <= self.N*self.N+self.N-1:
            block = goal+1-self.N*self.N
            if self.getB(goal, S, randomorder, currentState, bookkeep, block):
                if tuple(currentState) in bookkeep:
                    l = list(bookkeep[tuple(currentState)])
                    if isinstance(l[0], int):
                        l[0] = (l[0], l[1])
                        l[1] = (goal, self.action)
                        bookkeep[tuple(currentState)] = l
                    else :
                        l.append((goal, self.action))
                        bookkeep[tuple(currentState)] = l
                else:
                    bookkeep[tuple(currentState)] = (goal, self.action)
                return True


        # if clear block:
        #     if hold block in currentState:
        #         release block 
        #     else if on b1 block in currentState:
        #         unstack b1 block
        if goal >= self.N*self.N+self.N and goal <= self.N*self.N+2*self.N-1:
            block = goal + 1 - self.N - self.N*self.N
            if currentState[self.N*self.N+(2*self.N)+block-1]==1:
                if self.getB(goal, S, randomorder, currentState, bookkeep, block):
                    if tuple(currentState) in bookkeep:
                        l = list(bookkeep[tuple(currentState)])
                        if isinstance(l[0], int):
                            l[0] = (l[0], l[1])
                            l[1] = (goal, self.action)
                            bookkeep[tuple(currentState)] = l
                        else :
                            l.append((goal, self.action))
                            bookkeep[tuple(currentState)] = l
                    else:
                        bookkeep[tuple(currentState)] = (goal, self.action)
                    return True

            else :
                for b1 in range(1, self.N+1):
                    if currentState[(b1-1)*self.N+(block-1)]==1:          
                        if self.getC(goal, S, randomorder, currentState, bookkeep, b1, block):
                            if tuple(currentState) in bookkeep:
                                l = list(bookkeep[tuple(currentState)])
                                if isinstance(l[0], int):
                                    l[0] = (l[0], l[1])
                                    l[1] = (goal, self.action)
                                    bookkeep[tuple(currentState)] = l
                                else :
                                    l.append((goal, self.action))
                                    bookkeep[tuple(currentState)] = l
                            else:
                                bookkeep[tuple(currentState)] = (goal, self.action)
                            return True


        # if hold block:
        #     if ontable block in currentState:
        #         pick block
        #     else if on block b1 in currentState:
        #         unstack block b1
        if goal >= self.N*self.N+2*self.N and goal <= self.N*self.N+3*self.N-1:
            block = goal+1-(2*self.N)-(self.N*self.N)
            if currentState[self.N*self.N+block-1]==1:
                if self.getA(goal, S, randomorder, currentState, bookkeep, block):
                    if tuple(currentState) in bookkeep:
                        l = list(bookkeep[tuple(currentState)])
                        if isinstance(l[0], int):
                            l[0] = (l[0], l[1])
                            l[1] = (goal, self.action)
                            bookkeep[tuple(currentState)] = l
                        else :
                            l.append((goal, self.action))
                            bookkeep[tuple(currentState)] = l
                    else:
                        bookkeep[tuple(currentState)] = (goal, self.action)
                    return True

            else :
                for b1 in range(1, self.N+1):
                    if currentState[(block-1)*self.N+(b1-1)]==1:          
                        if self.getC(goal, S, randomorder, currentState, bookkeep, block, b1):
                            if tuple(currentState) in bookkeep:
                                l = list(bookkeep[tuple(currentState)])
                                if isinstance(l[0], int):
                                    l[0] = (l[0], l[1])
                                    l[1] = (goal, self.action)
                                    bookkeep[tuple(currentState)] = l
                                else :
                                    l.append((goal, self.action))
                                    bookkeep[tuple(currentState)] = l
                            else:
                                bookkeep[tuple(currentState)] = (goal, self.action)
                            return True


        # if on blocka blockb:
        if goal >= 0 and goal <= self.N*self.N-1:
            if self.getD(goal, S, randomorder, currentState, bookkeep):
                if tuple(currentState) in bookkeep:
                    l = list(bookkeep[tuple(currentState)])
                    if isinstance(l[0], int):
                        l[0] = (l[0], l[1])
                        l[1] = (goal, self.action)
                        bookkeep[tuple(currentState)] = l
                    else :
                        l.append((goal, self.action))
                        bookkeep[tuple(currentState)] = l
                else:
                    bookkeep[tuple(currentState)] = (goal, self.action)
                return True

        # if empty:
        #     if hold block in currentState:
        #         release block
        if goal == self.N*self.N+(3*self.N):
            for x in range(1,self.N+1):
                if currentState[self.N*self.N+2*self.N+x-1]==1:
                    if self.getB(goal, S, randomorder, currentState, bookkeep, x):
                        if tuple(currentState) in bookkeep:
                            l = list(bookkeep[tuple(currentState)])
                            if isinstance(l[0], int):
                                l[0] = (l[0], l[1])
                                l[1] = (goal, self.action)
                                bookkeep[tuple(currentState)] = l
                            else :
                                l.append((goal, self.action))
                                bookkeep[tuple(currentState)] = l
                        else:
                            bookkeep[tuple(currentState)] = (goal, self.action)
                        return True

        return False



    def getSuccessors(self, state):
        """
        Returns successor states, and the actions they require.
        Returns list of (state, action)
        """
        state = list(state)
        successors = []

        for block in range(1, (self.N)+1):
            if state[(self.N)*(self.N)+block-1]==1 and state[(self.N)*(self.N)+(self.N)+block-1]==1 and state[((self.N)*(self.N))+(3*(self.N))]==1 :
                action = "pick "+str(block)
                newstate = copy.deepcopy(state)
                newstate[(self.N)*(self.N)+(2*(self.N))+block-1] = 1
                newstate[(self.N)*(self.N)+(self.N)+block-1] = 0
                newstate[(self.N)*(self.N)+(3*(self.N))] = 0
                newstate[(self.N)*(self.N)+block-1] = 0
                successors.append((tuple(newstate), action))

            if (state[(self.N)*(self.N)+(2*(self.N))+block-1]==1 ):
                action = "release "+str(block)
                newstate = copy.deepcopy(state)
                newstate[(self.N)*(self.N)+(2*(self.N))+block-1] = 0
                newstate[(self.N)*(self.N)+(self.N)+block-1] = 1
                newstate[(self.N)*(self.N)+(3*(self.N))] = 1
                newstate[(self.N)*(self.N)+block-1] = 1
                successors.append((tuple(newstate), action))

        for blocka in range(1, (self.N)+1):
            for blockb in range (1, (self.N)+1):
                if (blocka == blockb):
                    continue

                if (state[(blocka-1)*(self.N)+(blockb-1)]==1 and state[(self.N)*(self.N)+(self.N)+blocka-1]==1 and state[((self.N)*(self.N))+(3*(self.N))]==1):
                    action = "unstack "+str(blocka)+" "+str(blockb)
                    newstate = copy.deepcopy(state)
                    newstate[(self.N)*(self.N)+(2*(self.N))+blocka-1] = 1
                    newstate[(self.N)*(self.N)+(self.N)+blockb-1] = 1
                    newstate[(blocka-1)*(self.N)+(blockb-1)] = 0
                    newstate[(self.N)*(self.N)+(3*(self.N))] = 0
                    newstate[(self.N)*(self.N)+(self.N)+blocka-1] = 0
                    successors.append((tuple(newstate), action))

                if (state[(self.N)*(self.N)+(self.N)+blockb-1]==1 and state[(self.N)*(self.N)+(2*(self.N))+blocka-1]==1):
                    action = "stack "+str(blocka)+" "+str(blockb)
                    newstate = copy.deepcopy(state)
                    newstate[(self.N)*(self.N)+(2*(self.N))+blocka-1] = 0
                    newstate[(self.N)*(self.N)+(self.N)+blockb-1] = 0
                    newstate[(blocka-1)*(self.N)+(blockb-1)] = 1
                    newstate[(self.N)*(self.N)+(3*(self.N))] = 1
                    newstate[(self.N)*(self.N)+(self.N)+blocka-1] = 1
                    successors.append((tuple(newstate), action))

        return successors




def breadthFirstSearch(problem):
    
    state = problem.getStartState()
    
    #Frontier is a queue which stores state
    frontier = Queue()
    frontier.push(state)
    
    #fron is a dictionary, where fron[state] stores (parent, action), where action is the action from parent to reach state
    fron = {}
    #The parent and action of the initial state is kept as None
    fron[state] = (None, None)
    
    #explored is a dictionary, where explored[state] stores (parent, action), where action is the action from parent to reach state
    explored = {}
    #Initially the parent is kept as None
    parent = None
    
    n=0

    while 1:
        # print state
        #If frontier is empty before reaching the goal state, no path exists, return empty list    
        if frontier.isEmpty():
            print "No path to reach the goal state\n"
            return []
            
        #Pop a state from the frontier list        
        state = frontier.pop()
        n+=1;
            
        #If the state is a goal state, then return the actions that were needed to get from the intitial state to this state
        #We trace back the actions using explored dictionary
        #We have to reverse the sequence of actions, because we had traced back, so we use a temp list
        if problem.isGoalState(state):
            actions = []
            temp = []
            (parent, action) = fron[state]
            while parent != None:
                actions.append(action)
                state = parent
                (parent, action) = explored[state]
            while actions:
                temp.append(actions.pop())

            fout = open(sys.argv[2], 'w')
            fout.write(str(len(temp)))
            fout.write("\n")

            for a in temp:
                fout.write(a+"\n")

            print "No of nodes expanded = ",n
            return temp    

        
        #Remove the state from fron dictionary and add it to explored dictionary
        explored[state] = fron.pop(state)
        #The current state acts like parent and its successors are extracted
        parent = state
        successors = problem.getSuccessors(parent)

        # print state
        # print successors

        #Adding the successors in the frontier list
        #If a succesor state is in explored dictionary, nothing is done
        #If a successor state is not in explored and fron dictionary, then it is added to frontier and updated in fron dictionary
        for x in successors:
            (state, action) = x
            if state not in explored and state not in fron:
                frontier.push(state)
                fron[state] = (parent, action)
    
    print "No of nodes expanded = ",n


#Heuristic for the problem
def heuristic (state, problem):
    return problem.checkingoal(state)
    


def aStarSearch(problem):
    """Search the node that has the lowest combined cost and heuristic first."""
    
    state = problem.getStartState()

    #Frontier is a priority queue which stores state, the priority is the pathcost + heuristic
    frontier = PriorityQueue()
    frontier.push(state, 0 + heuristic(state, problem))
    
    #fron is a dictionary, where fron[state] stores (parent, action), where action is the action from parent to reach state
    fron = {}
    #The parent and action of the initial state is kept as None
    fron[state] = (None, None, 0)

    #explored is a dictionary, where explored[state] stores (parent, action), where action is the action from parent to reach state
    explored = {}
    #Initially the parent is kept as None
    parent = None
    
    n=0
    while 1:
        #If frontier is empty before reaching the goal state, no path exists, return empty list
        if frontier.isEmpty():
            print "No path to reach the goal state\n"
            return []
        
        #Pop a state from the frontier list
        state = frontier.pop()
        n+=1     
        #If the state is a goal state, then return the actions that were needed to get from the intitial state to this state
        #We trace back the actions using explored dictionary
        #We have to reverse the sequence of actions, because we had traced back, so we use a temp list
        if problem.isGoalState(state):
            actions = []
            temp = []
            (parent, action, pathcost) = fron[state]
            while parent != None:
                actions.append(action)
                state = parent
                (parent, action, pathcost) = explored[state]
            while actions:
                temp.append(actions.pop())
            
            fout = open(sys.argv[2], 'w')
            fout.write(str(len(temp)))
            fout.write("\n")

            for a in temp:
                fout.write(a+"\n")

            print "No of nodes expanded = ", n
            return temp      
        
        #Remove the state from fron dictionary and add it to explored dictionary
        explored[state] = fron.pop(state)
        #The current state acts like parent, its patchost is taken in parentpathcost, and its successors are extracted
        parent = state
        parentpathcost = explored[parent][2]
        successors = problem.getSuccessors(parent)
        
        #Adding the successors in the frontier list, 
        #The pathcost of this state = pathcost till parentstate + pathcost from parent to this state
        #The priority is the pathcost + heuristic value
        #If a succesor state is in explored dictionary, nothing is done
        #If a successor state is not in explored and fron dictionary, then it is updated in frontier and updated in fron dictionary
        #Otherwise if a succesor state is not in explored but in fron dictionary, 
        #Then, it is updated in dictionary in frontier,
        #Its parent and cost is updated in fron dictionary if its newpathcost is less than existingpathcost
        for x in successors:
            (state, action) = x
            pathcost = parentpathcost + 1
            if state not in explored:
                frontier.update(state, pathcost + heuristic(state, problem))
                if state in fron:
                    existingpathcost = fron[state][2]                    
                    if pathcost < existingpathcost:
                        fron[state] = (parent, action, pathcost)                    
                else:
                    fron[state] = (parent, action, pathcost)



# Goal stack planning
def goalstackplanning(problem):
    
    # bookeep to keep track of the (state, goal, relevant action chosen) triple
    # For a given state, given goal to be satisfied, the same relevant action won't be chosen.
    bookkeep = {}

    # For each conjuct of subgoals, it keeps track of the ordering of the subgoals tried.
    # The same ordering for a subgoal conjuct won't be chosen again
    stateordering = {}

    number = problem.N
    actionplan = []
    initialState = problem.getStartState()

    goalState = problem.getGoalState()
    S = Stack()

    currentState = copy.deepcopy(initialState)
    currentState = list(currentState)

    goal = []

    for i in range(0, len(goalState)):
        if goalState[i]==1:
            goal.append(i)

    # Push goals onto stack
    S.push(goal)
    # Push each predicate onto the stack
    for i in range(0, len(goal)):
        S.push(goal[i])

    # While stack is not empty
    while not S.isEmpty():

    	# Pop element on the top of the stack
        x = S.pop()

        # If element is a conjuct goal, if true , then continue
        # If false, select an ordering of the subgoals and push on the stack (After checking uniqueness of the ordering from bookkeep list)
        if isinstance(x, (list, tuple)):
            for i in range(0, len(x)):
                if tuple(currentState)[x[i]]==0:
                    allgoals = copy.deepcopy(x)
                    # Select an order of subgoals and push on the stack
                    S.push(x)
                    allgoals = list(allgoals)

                    if tuple(currentState) in stateordering:
                        ways = list(itertools.permutations(allgoals))
                        l = stateordering[tuple(currentState)]

                        if isinstance(l[0], int):  

                            flag = 0
                            for allgoals in ways:
                                if tuple(allgoals) != l:
                                    flag = 1
                                    break

                            if flag == 0:
                                continue
                                print "No ordering left"
                                return

                        else:
                            flag = 0
                            for allgoals in ways:
                                if tuple(allgoals) not in l:
                                    flag = 1
                                    break

                            if flag == 0:
                                continue
                                print "No ordering left"
                                return


                    if tuple(currentState) in stateordering:
                        l = list(stateordering[tuple(currentState)])
                        if isinstance(l[0], int):
                            x = tuple(l)
                            del l
                            l = []
                            l.append(x)
                            l.append(tuple(allgoals))
                            stateordering[tuple(currentState)] = tuple(l)
                        else:
                            l.append(tuple(allgoals))
                            stateordering[tuple(currentState)] = tuple(l)
                    else:
                        stateordering[tuple(currentState)] = tuple(allgoals)

                    for i in range (0, len(allgoals)):
                        S.push(allgoals[i])
                    break


        # Else if predicate, if true : do nothing
        # If false, Push relevant action a onto the stack
		# Push Precond(a) onto the stack
		# Push each predicate of Precond(a) on to the stack
        elif isinstance(x, int):
            if tuple(currentState)[x]==1:
                continue
            else:
                x = problem.getRelevantState(x, S, currentState, bookkeep)
                if (not x):
                    continue

        # Else if element is an action, add action a to the actionplan.
        # Also, change the currentstate according to the action.
        else:
            actionplan.append(x)
            matchObj = re.match( r'pick (\d*)', x, re.M|re.I)
            matchObj1 = re.match( r'release (\d*)', x, re.M|re.I)
            matchObj2 = re.match( r'unstack (\d*) (\d*)', x, re.M|re.I)
            matchObj3 = re.match( r'stack (\d*) (\d*)', x, re.M|re.I)

            if matchObj :
                block = int(matchObj.group(1))
                currentState[number*number+2*number+block-1] = 1
                currentState[(number*number)+(number)+block-1] = 0
                currentState[(number*number)+(3*(number))] = 0
                currentState[(number*number)+block-1] = 0


            elif matchObj1:
                block = int(matchObj1.group(1))
                currentState[(number)*(number)+(2*(number))+block-1] = 0
                currentState[(number)*(number)+(number)+block-1] = 1
                currentState[(number)*(number)+(3*(number))] = 1
                currentState[(number)*(number)+block-1] = 1


            elif matchObj2:
                blocka = int(matchObj2.group(1))
                blockb = int(matchObj2.group(2))
                currentState[(number)*(number)+(2*(number))+blocka-1] = 1
                currentState[(number)*(number)+(number)+blockb-1] = 1
                currentState[(blocka-1)*(number)+(blockb-1)] = 0
                currentState[(number)*(number)+(3*(number))] = 0
                currentState[(number)*(number)+(number)+blocka-1] = 0

            elif matchObj3 :
                blocka = int(matchObj3.group(1))
                blockb = int(matchObj3.group(2))
                currentState[(number)*(number)+(2*(number))+blocka-1] = 0
                currentState[(number)*(number)+(number)+blockb-1] = 0
                currentState[(blocka-1)*(number)+(blockb-1)] = 1
                currentState[(number)*(number)+(3*(number))] = 1
                currentState[(number)*(number)+(number)+blocka-1] = 1

    fout = open(sys.argv[2], 'w')
    fout.write(str(len(actionplan)))
    fout.write("\n")

    for a in actionplan:
        fout.write(a+"\n")

    return actionplan



# Main execution of the program
if (len(sys.argv) != 3):
    print "To run the program : python main.py <input_file> <output_file>"
    exit(0)

fin = open(sys.argv[1] ,"r")

number = int (fin.readline().strip())
algo = fin.readline().strip()

prob = problem()
if algo=="f":
    print "Breadth first search"
    breadthFirstSearch(prob)
elif algo=="a":
    print "A* search"
    aStarSearch(prob)
elif algo=="g":
    print "Goal stack planning"
    goalstackplanning(prob)
else:
    print "Please mention a valid planning approach in the text file (f/a/g)."