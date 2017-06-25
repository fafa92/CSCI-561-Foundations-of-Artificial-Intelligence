import os
import re
from copy import deepcopy
################ Move validation function ##############
def IsValid(node, player , new_board):
	if new_board[node[0]][node[1]] !='*':
		return []
	if player == 'O':
		regex = r"^X+O"
	else:
		regex = r"^O+X"
	
	result = []
	
	i = node[0]
	j = node[1]
	
	tuples = [	[-1,0],[-1,1],[0,1],[1,1],
				[1,0],[1,-1],[0,-1],[-1,-1]	]
	
	for t in tuples:
		indexs = []
		temp = ''
		
		i = node[0] + t[0]
		j = node[1] + t[1]
		
		# We should see opponent's cell in near current node
		while ( i<8 and i>=0 ) and ( j<8 and j>=0 ):
			
			temp += new_board[i][j]
			
			indexs.append((i,j))
			
			i += t[0]
			j += t[1]
			# after that we saw opponent's cell we should see player's cell
				
		temp = re.match(regex,temp,0)
		if temp != None	:
			result.append(indexs[ temp.start() : temp.end() ] )			
			
	return result
############# End move validation function #############
class Movement:
	def __init__(self ,node ,index):
		self.node = node
		self.index = index
		
		
def disp(board):
	t = ''
	for i in range(0,8):
		for j in range(0,8):
			t += board[i][j]
		t += '\n'
	print(t)

def move(movement ,board, player):
	
	node = movement.node
	index = movement.index
	new_board = deepcopy(board)
	new_board[node[0]][node[1]] = player
	
	for s in index:
		for t in s:
			new_board[t[0]][t[1]] = player
	#i = input('')
	return new_board
	
class Solution:
	def __init__(self, value, board):
		self.value = value
		self.board = board

class Child:
	def __init__(self, node, board):
		self.node = node
		self.board = board
		
def IsFill(board):
	for i in range(0,8):
		for j in range(0,8):
			if board[i][j] == '*':
				return False
	return True

	
Weights = [ [99,-8,8,6,6,8,-8,99],
			[-8,-24,-4,-3,-3,-4,-24,-8],
			[8,-4,7,4,4,7,-4,8],
			[6,-3,4,0,0,4,-3,6],
			[6,-3,4,0,0,4,-3,6],
			[8,-4,7,4,4,7,-4,8],
			[-8,-24,-4,-3,-3,-4,-24,-8],
			[99,-8,8,6,6,8,-8,99]  ]
################################################			
Board = [	['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],
			['*','*','*','*','*','*','*','*'],	]
			
first_player = ''
second_player = ''
depth = 0

# slt save the best next move
slt = Solution(float('-inf'),None) # value , Board

global continuous_pass # for count passes 
continuous_pass = 0

################ Prepare to output ###############
out_str = []

def write(node, d, value, alpha, beta, board):
	temp = '\n'
	if d == 1:
		if value > slt.value:
			slt.value = value
			slt.board = board
	
	if node == 'root':
		temp += "root"
	elif node == 'pass':
		temp += 'pass'
	else:
		temp += chr(node[1] + 97)
		temp += str(node[0] + 1)
	temp += ','
	
	temp += str(d)
	temp += ','
	
	temp += str(value)
	temp += ','
	
	temp += str(alpha)
	temp += ','
	
	temp += str(beta)
	
	if 'inf' in temp:
		temp = temp.replace('inf', 'Infinity')
	out_str.append(temp)


################# Evaluation function ##################
def E(board):
		
	sigma_1 = 0
	sigma_2 = 0
	
	for i in range(0,8):
		for j in range(0,8):
		
			if board[i][j] == 'O':
				sigma_1 += Weights[i][j]
				
			elif board[i][j] == 'X':
				sigma_2 += Weights[i][j]
	
	if first_player == 'X':
		return sigma_2 - sigma_1
	else:
		return sigma_1 - sigma_2

	
def AlphaBeta(board, d, IsMaxNode, alpha, beta, node):
	
	global continuous_pass

	if (d >= depth) or (continuous_pass == 2) or (IsFill(board)):

		value = E(board)
		write(node, d, value, alpha, beta, board)
		return value
		
		
	elif IsMaxNode:
	
		player = first_player
		opponent = second_player
		
		value = float('-inf')
		
		children = []
		for i in range(0,8):
			for j in range(0,8):
				
				index = IsValid([i,j], player , board)
				if index != []:
					
					new_child = Movement([i,j],index)
				
					new_board = move(new_child , deepcopy(board), player)
					
					ch = Child([i,j],new_board)
					
					children.append(ch)
		

		if children != []: # If there is any valid move
			for ch in children:
				
				continuous_pass = 0
				
				write(node ,d, value, alpha, beta, board)	
				
				child_value = AlphaBeta(ch.board, d + 1, False, deepcopy(alpha), deepcopy(beta), ch.node)	
				
				value = max(child_value, value)

				if max(value, alpha) < beta:
					alpha = max(value, alpha)
				else:
					break
					
			write(node, d, value, alpha, beta, board)	
			
		else:# If there is no valid move we should pass
			continuous_pass += 1
			
			write(node, d, value, alpha, beta, board)
			
			child_value = AlphaBeta(deepcopy(board), d + 1, False, deepcopy(alpha), deepcopy(beta), 'pass')
			
			value = max(child_value, value)
			
			if max(value, alpha) < beta:
				alpha = max(value, alpha)
			
			write(node, d, child_value, alpha, beta, board)
		
		return value
	else:
		
		player = second_player
		opponent = first_player

		value = float('+inf')
		
		children = []
		for i in range(0,8):
			for j in range(0,8):
				
				index = IsValid([i,j], player , board)
				if index != []:
					
					new_child = Movement([i,j],index)
				
					new_board = move(new_child , deepcopy(board), player)
					
					ch = Child([i,j],new_board)
					
					children.append(ch)

		if children != []:
			for ch in children:
				
				continuous_pass = 0
				
				write(node ,d, value, alpha, beta, board)	
				
				child_value = AlphaBeta(ch.board, d + 1, True, deepcopy(alpha), deepcopy(beta), ch.node)
			
				value = min(child_value, value)

				beta = min(value, beta)

				if min(value, beta) > alpha:
					beta = min(value, beta)
				else:
					break
				
			write(node, d, value, alpha, beta, board)
			
		else:
			continuous_pass += 1
			
			write(node, d, value, alpha, beta, board)
			
			child_value = AlphaBeta(deepcopy(board), d + 1, True, deepcopy(alpha), deepcopy(beta), 'pass')
			
			value = min(child_value, value)
			
			if min(value, beta) > alpha:
				beta = min(value, beta)
				
			write(node, d, child_value, alpha, beta, board)
		
		return value
		
############ End of function ###############	
	
########## Read input file and set initial values########

input = open('C:\Users\Faraz\Downloads\Compressed\New folder (4)\Sample Test Cases\TestCase 2\input.txt','r').read().split('\n')

first_player = input[0]

if first_player == 'X':
	second_player = 'O'
else:
	second_player = 'X'

depth = int(input[1])

for i in range(2,10):
	for j in range(0,8):
		Board[i-2][j] = input[i][j]

slt.board = deepcopy(Board)		
############################################################

AlphaBeta (Board, 0, True, float('-Inf'), float('+Inf'), 'root')

########## Write to output file ############

out = open('C:\Users\Faraz\Downloads\Compressed\New folder (4)\Sample Test Cases\TestCase 2\out.txt','w')

for i in range(0,8):
	for j in range(0,8):
		out.write(slt.board[i][j])
	out.write('\n')

out.write('Node,Depth,Value,Alpha,Beta')

for i in range(len(out_str)):
	out.write(out_str[i])
out.close()

