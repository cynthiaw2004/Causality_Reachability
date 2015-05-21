import sys
import os
scriptpath = "/Users/cynthia/Desktop/Causality/virtual_environment_test/gunfolds/tools"
#scriptpath = "/na/homes/cfreeman/Documents/virtual_test_environment/gunfolds/tools"
sys.path.append(os.path.abspath(scriptpath))
import traversal, bfutils, graphkit,unknownrate,comparison
from itertools import permutations,product,combinations,chain
from Levenshtein import hamming
import numpy as np
from numpy.random import randint
import zickle as zkl
import matplotlib.pyplot as plt
from collections import defaultdict

#input: number of vertices
#output: list of all possible ground truths with n nodes 
#(only single directed edges allowed)
def determine_domain(n):
	vertices = [x+1 for x in range(n)]
	#determine all single directed edges
	single_directed_edge_list = list(product(vertices,vertices))
	#determine all possible graphs that can be formed 
	allgraphs = chain.from_iterable(combinations(single_directed_edge_list, r) for r in range(len(single_directed_edge_list)+1))
	#now to convert to dictionary form that sergey uses
	g = generate_Empty_Graph(n)
	glist = []
	for i in allgraphs:
		if i != ():
			for e in i:
				e = (str(e[0]),str(e[1]))
				if g[e[0]].get(e[1]) == None:
					g[e[0]][e[1]] = set([(0,1)])
				else: #entry already exists
					g[e[0]][e[1]].add((0,1))
		glist.append(g)
		g = generate_Empty_Graph(n)
	return glist

#input: number of vertices
#output: the codomain-list of all possible graphs with n many vertices
#(both directed and bidirected edges allowed)
def determine_codomain(n):
	vertices = [x+1 for x in range(n)]
	#determine all single directed edges
	single_directed_edge_list = list(product(vertices,vertices))
	#determine all bidirected edges
	bidirected_edge_list = list(combinations(vertices,2))
	bidirected_edge_list_0 = []
	for k in bidirected_edge_list:
		(x,y) = k
		bidirected_edge_list_0.append((x,y,'bidirected')) #make these distinct from single direct edges
	#determine all possible graphs that can be formed 
	single_directed_edge_set = set(single_directed_edge_list)
	bidirected_edge_set = set(bidirected_edge_list_0)
	alledges = single_directed_edge_set | bidirected_edge_set
	allgraphs = chain.from_iterable(combinations(alledges, r) for r in range(len(alledges)+1))
	#now to convert to dictionary form
	g = generate_Empty_Graph(n)
	glist = []
	for i in allgraphs:
		if i != ():
			for e in i:
				if len(e) == 2:
					e = (str(e[0]),str(e[1]))
					if g[e[0]].get(e[1]) == None:
						g[e[0]][e[1]] = set([(0,1)])
					else: #entry already exists
						g[e[0]][e[1]].add((0,1))
				else: #len(e) ==3
					e = (str(e[0]),str(e[1]),str(e[2]))
					if g[e[0]].get(e[1]) == None:
						g[e[0]][e[1]] = set([(2,0)])
					else: 
						g[e[0]][e[1]].add((2,0))
		glist.append(g)
		g = generate_Empty_Graph(n)
	return glist

#input: a graph GT
#output: all undersamples of graph GT up to UMAX in a list
#note: we have edited the form:
#if a->b has (2,0) and b->a has (2,0) (highly redundant and super dumb)
#change it so that a->b has (2,0) but b->a doesnt have (2,0)
def determine_reachable_graphs_edited(GT):
	unedited = bfutils.call_undersamples(GT)
	for G in unedited:
		for outerkey in G.keys():
		#print "from:",outerkey
			for innerkey in G[outerkey].keys():
				#print "to:",innerkey
				#print "sets:", G[outerkey][innerkey]
				if (2,0) in G[outerkey][innerkey] and (2,0) in G[innerkey][outerkey]: 
					if len(G[innerkey][outerkey]) > 1: #(2,0) isn't the only one in the set
						G[innerkey][outerkey].remove((2,0))
					else: #(2,0) is the only one in the set
						del G[innerkey][outerkey]
	return unedited

#input: number of vertices
#output: list of all reachable graphs from all possible gts with n nodes
def determine_all_reachable_graphs(n):
	all_reachable_graphs = []
	gts = determine_domain(n)
	for graph in gts:
		reachable_graphs = determine_reachable_graphs_edited(graph)
		for rg in reachable_graphs:
			if rg not in all_reachable_graphs:
				all_reachable_graphs.append(rg)
	return all_reachable_graphs

#input: number of vertices
#output: list of all unreachable graphs from all possible gts with n nodes
def determine_all_unreachable_graphs(n):
	codomainList = determine_codomain(n)
	reachableList = determine_all_reachable_graphs(n)
	
	unreachableList = [item for item in codomainList if item not in reachableList]

	#unreachableList = []
	#for graph in codomainList:
	#	if i not in reachableList and i not in unreachableList:
	#		unreachableList.append(i)
	return unreachableList

#input: number of vertices
#output: cardinality of domain
def determine_domain_cardinality(n):
	exponent = n**2
	return 2**exponent

#input: number of vertices
#output: cardinality of the codomain 
def determine_codomain_cardinality(n):
	exponent = n**2 + choose(n,2)
	return 2**exponent

#input: number of vertices
#ouput: empty graph dictionary for n vertices
def generate_Empty_Graph(n):
	g = {}
	for i in range(n):
		g[str(i+1)] = {} #use str to match sergey's call undersamples func
	return g

#input: a graph G
#output: a dictionary where key = vertex and value = in degree
def determine_in_degrees(G):
	in_degree_dict = {}
	for i in range(len(G)):
		in_degree_dict[str(i+1)] = 0
	for outerkey in G.keys():
		#print "\n"
		#print "from:",outerkey
		for innerkey in G[outerkey].keys():
			#print "to:",innerkey
			#print G[outerkey][innerkey]
			if (0,1) in G[outerkey][innerkey]:
				in_degree_dict[innerkey] = in_degree_dict[innerkey] + 1	
			if (2,0) in G[outerkey][innerkey]: #take into account bidirected edges
				in_degree_dict[outerkey] = in_degree_dict[outerkey] + 1
				in_degree_dict[innerkey] = in_degree_dict[innerkey] + 1
	return in_degree_dict

#input: a graph G
#output: a dictionary where key = vertex and value =  out degree
def determine_out_degrees(G):
	out_degree_dict = {}
	for i in range(len(G)):
		out_degree_dict[str(i+1)] = 0
	for outerkey in G.keys():
		for innerkey in G[outerkey].keys():
			if (0,1) in G[outerkey][innerkey]:
				out_degree_dict[outerkey] = out_degree_dict[outerkey] + 1	
			if (2,0) in G[outerkey][innerkey]: #take into account bidirected edges
				out_degree_dict[outerkey] = out_degree_dict[outerkey] + 1
				out_degree_dict[innerkey] = out_degree_dict[innerkey] + 1
	return out_degree_dict

#input: an UNREACHABLE graph H and the ground truth G
#output: the nearest reachable graphs
def determine_nearest_reachable_graph(H,G):
	distances = []
	all_reachable_graphs = determine_all_reachable_graphs(len(G))
	for graph in all_reachable_graphs:
		distances.append(determine_edit_distance(graph,H))
	distancesnp = np.array(distances)
	indices_of_nearest_graphs = np.where(distancesnp == distancesnp.min())
	return [all_reachable_graphs[index] for index in indices_of_nearest_graphs]

#input: two graphs G1 and G2
#ouput: the hamming distance (the number of differing characters) between the two graphs
def determine_edit_distance(G1,G2):
	G1str = str(graph2str(G1))
	G2str = str(graph2str(G2))
	#G1str and G2str MUST have same length
	return hamming(G1str,G2str)

#input: n, k
#ouput n choose k
def choose(n, k):
    if 0 <= k <= n:
        ntok = 1
        ktok = 1
        for t in xrange(1, min(k, n - k) + 1):
            ntok *= n
            ktok *= t
            n -= 1
        return ntok // ktok
    else:
        return 0

#input: a graph, start node, end node
#output: return a list of all paths from start node to end node in the graph
def find_all_paths(graph, start, end,path = []):
	path = path + [start]
	if start == end:
	    return [path]
	if not graph.has_key(start):
	    return []
	paths = []
	for node in graph[start]:
	    if node not in path:
	        newpaths = find_all_paths(graph, node, end,path)
	        for newpath in newpaths:
	        	paths.append(newpath)
	#print paths
	return paths

#input: a graph, start node, end node (start and end node are strings)
#output: return a list of all the shortest paths from start node to end node in the graph
def find_shortest_paths(graph, start, end, path=[]):
	all_paths = find_all_paths(graph,start,end,path = [])
	if all_paths:
		length_of_shortest_path = len(min(all_paths))
		shortest_paths = []
		for path in all_paths:
			if len(path) == length_of_shortest_path:
				shortest_paths.append(path)
		return shortest_paths
	else:
		return []

#X is a pivotal node wrt distinct nodes Y and Z
#if X lies on every SHORTEST path between Y and Z and
#X is not equal to Y or Z
#input: graph,x (the node we check for pivotality),y,z (x,y,z are strings)
#output: T if x is a pivotal node wrt y and x
#		 F if x is not a pivotal node wrt y and x
# 		 -1 if x=y or y=z or x=z
def determine_pivotal_x(graph,x,y,z):
	if x==y or y==z or x==z:
		return -1
	shortest_paths = find_shortest_paths(graph,y,z)
	if shortest_paths:
		for path in shortest_paths:
			if x not in path:
				return False
		return True
	return False

#X is a pivotal node if X is
#pivotal for every pair of distinct vertices Y and Z
#input: a graph and a node x to test for pivotality (str)
#output: T if x is pivotal in general
#		 F if x is not pivotal in general
def determine_all_pivotal_x(graph,x):
	#determine all pairs of distinct vertices
	number_of_nodes = len(graph)
	nodes = set([str(i) for i in range(1,number_of_nodes+1)])
	nodes = nodes - set([x])
	pairs = []
	for perm in permutations(nodes,2):
		#print perm
		pairs.append(perm)
	for pair in pairs:
		if determine_pivotal_x(graph,x,pair[0],pair[1]) == False:
			return False
	return True

#input: a graph in dictionary format
#output: a dictionary where key = node and value = T if node is pivotal
#and F if node is not pivotal
def determine_all_pivotal(graph):
	number_of_nodes = len(graph)
	nodes = set([i for i in range(1,number_of_nodes+1)])
	nodes_piv = {key:None for key in range(1,number_of_nodes+1)}
	for node in nodes:
		nodes_piv[node] = determine_all_pivotal_x(graph,str(node))
	return nodes_piv

#TO REPLACE SOON ONCE SERGEY PUSHES TO GITHUB
#input: a graph G
#output: string version of G
def graph2str(G):
    n = len(G)
    d = {((0,1),):'1', ((2,0),):'0',((2,0),(0,1),):'1',((0,1),(2,0),):'1'}
    A = ['0']*(n*n)
    for v in G:
        for w in G[v]:
            A[n*(int(v,10)-1)+int(w,10)-1] = d[tuple(G[v][w])]
    return ''.join(A)

#warning: 

#graph2str PRESERVES bidirected edges when converting to string
#but there is no function to convert back to dictionary
#safe to use with undersampled graphs but NOT ground truths

#g2num does NOT preserve bidirected edges when converting to string
#but there IS a function to convert back to dictionary (num2CG)
#safe to use with ground truths since ground truths do not
#have bidirected edges

##################testing area#######################################

#what fails: 
#in degree,
#out degree, 
#hamming distance between members 
#hamming distance between members and H, 
#to try: 
#pivotal nodes 
#centrality


#n = number of nodes
n = 3

all_reachable_graphs = determine_all_reachable_graphs(n)
i = 1
number_of_dict_with_T_r = 0
for graph in all_reachable_graphs:
	print "r: ",i
	pdict = determine_all_pivotal(graph)
	print pdict
	if sum(pdict.values())>0:
		number_of_dict_with_T_r = number_of_dict_with_T_r + 1
	i = i + 1
print "------------------"
all_unreachable_graphs = determine_all_unreachable_graphs(n)
j = 1
number_of_dict_with_T_ur = 0
for graph in all_unreachable_graphs:
	print "ur: ",j
	pdict = determine_all_pivotal(graph)
	print pdict
	if sum(pdict.values())>0:
		number_of_dict_with_T_ur = number_of_dict_with_T_ur + 1
	j = j + 1

print "number of reachable graphs with pivotal nodes: ",number_of_dict_with_T_r
print "number of unreachable graphs with pivotal nodes: ",number_of_dict_with_T_ur

