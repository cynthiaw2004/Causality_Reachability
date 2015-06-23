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
import networkx as nx 
import networkx.algorithms.isomorphism as iso

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
#output: list of all possible ground truths with n nodes that are SCCS
#(only single directed edges allowed)
def determine_SCC_domain(n):
	vertices = [x+1 for x in range(n)]	
	#determine all single directed edges
	single_directed_edge_list = list(product(vertices,vertices))
	#remove ring edges
	for x in range(n):
		if x+2 == n+1:
			single_directed_edge_list.remove((x+1,1))
		else:
			single_directed_edge_list.remove((x+1,x+2))
	#determine all possible graphs that can be formed 
	allgraphs = chain.from_iterable(combinations(single_directed_edge_list, r) for r in range(len(single_directed_edge_list)+1))
	#now to convert to dictionary form that sergey uses
	g = generate_ring_graph(n)
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
		g = generate_ring_graph(n)
	return glist

#input: number of vertices
#output: the codomain-list of all possible graphs with n many vertices
#(both directed and bidirected edges allowed)
#this function blows
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

#input: number of nodes in graph
#output: a list of all reachable graphs with n nodes
def determine_reachable_graphs(n):
	reachableList = []
	gts = determine_domain(n)
	for graph in gts:
		reachable_graphs = bfutils.call_undersamples(graph)[1:] #because 0 returns itself and that's dumb
		for rg in reachable_graphs:
			if rg not in reachableList:
				reachableList.append(rg)
	return reachableList

#input: number of nodes in graph
#output: a list of all reachable graphs with n nodes
def determine_SCC_reachable_graphs(n):
	reachableList = []
	gts = determine_SCC_domain(n)
	for graph in gts:
		reachable_graphs = bfutils.call_undersamples(graph)[1:] #because 0 returns itself
		for rg in reachable_graphs:
			if rg not in reachableList:
				reachableList.append(rg)
	return reachableList

#input: number of nodes, name of zickle file to save to
#output: none...we just make a zickle file of a list of the reachable graphs with n nodes
def make_rg_zickle(n,name):
	rgs = determine_reachable_graphs(n)
	zkl.save(rgs,name)

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

#input: number of vertices
#output: ring graph dictionary for n vertices
def generate_ring_graph(n):
	g = {}
	for i in range(1,n):
		g[str(i)] = {str(i+1): set([(0,1)])}
		g[str(n)] = {'1': set([(0,1)])} 
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

#input: a graph H (in codomain land)
#output: the nearest reachable graphs to H
def determine_nearest_reachable_graph(H):
	distances = []
	all_reachable_graphs = determine_reachable_graphs(len(H))
	for graph in all_reachable_graphs:
		distances.append(determine_edit_distance(graph,H))
	distancesnp = np.array(distances)
	indices_of_nearest_graphs = np.where(distancesnp == distancesnp.min())
	return [all_reachable_graphs[index] for index in indices_of_nearest_graphs]

#input: two graphs G1 and G2
#ouput: the hamming distance (the number of differing characters) between the two graphs
def determine_edit_distance(G1,G2):
	#TO EDIT!!!!!!!!!!!!!!!!!!!
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

#warning: not able to find cycles (start and end can't be equal)
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

#input: G^1 (domain graph)
#output: string version of G^1
#warning: this function does not take bidirected edges into account
def g2num(g):
    n = len(g)
    n2 = n**2 + n
    num = 0
    for v in range(1,n+1):
        for w in g[str(v)]:
            num |= (1<<(n2 - v*n - int(w,10)))
    return num

#input: G^u (codomain graph)
#output: string version of G^u 
def ug2num(g):
    n = len(g)
    n2 = n**2 + n
    num = 0
    num2 = 0
    mask = 0
    for v in g:
        for w in g[v]:
            if (0,1) in g[v][w]:
                mask = (1<<(n2 - int(v,10)*n - int(w,10)))
                num |= mask
            if (2,0) in g[v][w]: 
            	num2 |= mask
    return num, num2

#simple loop: directed cycle in which no node is repeated
#input: a graph, node
#output: return a list of all 
#		 directed cycles with no node repeats
#		 in the graph starting (and obviously ending) from c_node
def find_all_cycles(graph,c_node):
	if not graph.has_key(c_node):
	    return []
	all_paths = []
	for node in graph[c_node]:
		partial_path_1 = [c_node]
		partial_paths_2 = find_all_paths(graph,node,c_node)
		for partial_path_2 in partial_paths_2:
			full_path = partial_path_1 + partial_path_2
			all_paths.append(full_path)
	return all_paths

#simple loop: directed cycle in which no node is repeated
#input: a graph
#output: return a dictionary where key = node, value = array of simple loop lengths
def find_simple_loop_lengths(graph):
	cycle_lengths = {} #key = node, value = array of simple loop lengths
	for node in graph:
		lengths = []
		cycles = find_all_cycles(graph,node)
		for cycle in cycles:
			lengths.append(len(cycle))
		cycle_lengths[node] = lengths
	return cycle_lengths

#input: a graph G
#output: a list containing all isomorphisms of G
def find_all_isomorphisms(G):
	num_vertices = len(G)
	string = ''
	for k in range(1,num_vertices+1):
		string = string + str(k)
	all_permutations = permutations(string)
	all_isos = []
	for permutation in all_permutations:
		#make isomorphism function mapping nodes to new ordering of nodes
		iso_func = {}
		i = 0
		for u in G:
			iso_func[u] = permutation[i]
			i = i + 1
		#make new isomorphic graphs
		new_isomorphic_G = generate_Empty_Graph(len(G))
		for start in G:
			inner_dict = {}
			for end in G[start]:
				inner_dict[iso_func[end]] = G[start][end]  
				new_isomorphic_G[iso_func[start]] = inner_dict 
				#print "check: ",new_isomorphic_G
		all_isos.append(new_isomorphic_G)
	return all_isos

#input: number of nodes
#output: a list of nonisomorphic reachable graphs
#def return_only_unique(n):
def return_only_unique(name):
	#rg = determine_reachable_graphs(n)
	rg = zkl.load(name)
	for item1 in rg:
		#delete all isomorphisms from rg
		all_isos = find_all_isomorphisms(item1)
		for item2 in all_isos:
			if item2 in rg and item1 != item2:
				rg.remove(item2)	
	return rg










#TO BE DELETED
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

##################testing area#######################################

#what fails: 
#in degree,
#out degree, 
#hamming distance between members 
#hamming distance between members and H, 
#pivotal nodes 
#centrality
#simple loop lengths


#TODO:
#dbn plot
#fix hamming distance stuff
#is there a way to get unreachable graphs quickly?


















