import sys
import os
scriptpath = "/Users/cynthia/Desktop/Causality/virtual_environment_test/gunfolds/tools"
#scriptpath = "/na/homes/cfreeman/Documents/virtual_test_environment/gunfolds/tools"
sys.path.append(os.path.abspath(scriptpath))
import traversal, bfutils, graphkit,unknownrate,comparison
from itertools import permutations,product,combinations,chain
import numpy as np
from numpy.random import randint
import zickle as zkl
import matplotlib.pyplot as plt
from collections import defaultdict
import networkx as nx 
import networkx.algorithms.isomorphism as iso
import copy
import pydot

#input: number of vertices
#output: list of all possible ground truths with n nodes 
#(only single directed edges allowed in domain graphs)
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
    #remove ring edges from all single directed edges list (since these will already be included)
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
#this function is sloooooowww
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
    g = generate_Empty_Graph(n) #so there can exist nodes that are empty
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

#input: a graph G
#output: a list containing all isomorphisms of G (includes relabeling issues with bidirected edges)
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
        #find all forms involving bidirected edges
        all_forms = find_all_forms_codomain_graph(new_isomorphic_G)
        for g in all_forms:
            all_isos.append(g)
    return all_isos

#input: number of nodes in graph
#output: a list of all reachable graphs with n nodes
def determine_reachable_graphs(n):
    reachableList = []
    gts = determine_domain(n)
    for graph in gts:
        reachable_graphs = bfutils.call_undersamples(graph)[1:] #because 0 returns itself and that's boring and we want undersampling rates higher than 1
        for rg in reachable_graphs:
            if rg not in reachableList:
                reachableList.append(rg)
    return reachableList

#input: number of nodes 
#output: a list of nonisomorphic reachable graphs
#def return_only_unique_rg(n):   
    #rg = determine_reachable_graphs(n)
################OR######################
#input: name of the zickle file of reachable graphs
#output: a list of nonisomorphic graphs
def return_only_unique_rg(name):
    rg = zkl.load(name)
    for item1 in rg:
        #delete all isomorphisms from rg
        all_isos = find_all_isomorphisms(item1)
        for item2 in all_isos:
            if item2 in rg and item1 != item2:
                rg.remove(item2)    
    return rg

#input: a codomain graph
#output: all possible forms of this codomain graph involving bidirected edges
def find_all_forms_codomain_graph(G):
	#determine unique bidirected edges of G
	unique_bidirected_edges = []
	for u in G:
		for v in G[u]:
			if (2,0) in G[u][v] and [v,u] not in unique_bidirected_edges:
				unique_bidirected_edges.append([u,v]) 
	#if there are no bidirected edges, there is only way to write this graph G
	if unique_bidirected_edges == []:
		return [G]
	else: #there are bidirected edges so there are multiple ways to write this graph G
		#make all pairings 
		all_pairings = product('buv',repeat = len(unique_bidirected_edges))
		#make all graph forms of G
		allforms = []
		for pairing in all_pairings:
			Gcopy = copy.deepcopy(G)
			for start in Gcopy:
				for end in Gcopy[start]:
					if [start,end] in unique_bidirected_edges:
						pair_index = unique_bidirected_edges.index([start,end])

						if pairing[pair_index] == 'b':
							#add (2,0) from start to end 
							Gcopy[start][end].add((2,0))
							#add (2,0) from end to start
							if start not in Gcopy[end]:
								Gcopy[end][start] = set([(2,0)])
							else:
								Gcopy[end][start].add((2,0)) 

						elif pairing[pair_index] == 'u':
							#add (2,0) from start to end
							Gcopy[start][end].add((2,0))
							#remove (2,0) from end to start
							if start in Gcopy[end]:
								Gcopy[end][start].discard((2,0)) 


						elif pairing[pair_index] == 'v':
							#add (2,0) from end to start
							if start not in Gcopy[end]:
								Gcopy[end][start] = set([(2,0)])
							else:
								Gcopy[end][start].add((2,0))	
							#remove (2,0) from start to end
							Gcopy[start][end].discard((2,0))
							
			#convert empty forms	
			itercopy = copy.deepcopy(Gcopy)
			for a in itercopy:
				for b in itercopy[a]:
					if Gcopy[a][b] == set([]):
						del Gcopy[a][b]

			allforms.append(Gcopy)
		return allforms

#input: number of nodes in graph 
#output: a list of all unique unreachable graphs with n nodes
#def determine_unreachable_graphs(n): #if zickle file of rgs is not created
		#rgs = determine_reachable_graphs(n) #if zickle file of rgs is not created
################OR######################
#input: name of zickle file of reachable graphs and number of nodes
#output: a list of all unique unreachable graphs with n nodes
def determine_unique_unreachable_graphs(name,n):
	#determine codomain
	codomain = determine_codomain(n) #SLOW
	#load up zkl file of all reachable graphs
	rgs = zkl.load(name)	
	#for every graph in reachable graphs, create all possible forms and remove from codomain
	for rg in rgs:
		allforms_graph = find_all_forms_codomain_graph(rg)
		for item in allforms_graph:
			while item in codomain:
				codomain.remove(item)
	#remove isomorphisms from codomain to get unique codomain
	for graph1 in codomain:
		all_isos = find_all_isomorphisms(graph1)
		for graph2 in all_isos:
			if graph2 in codomain and graph1 != graph2:
				codomain.remove(graph2)
	return codomain
 
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

#input: a graph g2 (in codomain land)
#output: the nearest reachable graphs to g2
def determine_nearest_reachable_graph_sergey(g2):
    s = traversal.v2g22g1(g2, capsize=100, verbose=False)
    if s: return s
    step = 1
    n = len(g2)
    v = bfutils.g2vec(g2)
    while True:
        l = hamming_neighbors(v,step) 
        c = 0
        for e in l:
            g = bfutils.vec2g(e,n)
            if not graphkit.scc_unreachable(g):
                s = traversal.v2g22g1(g, capsize=100, verbose=False)
            else:
                s = set()
            if s: return s
            c += 1
        if step > 4:
            return set()
        step += 1

#helper function for determine_nearest_reachable_graph_sergey
def hamming_neighbors(v, step):
    l = []
    for e in combinations(range(len(v)),step):
        b = copy.copy(v)
        for i in e: b[i] = int(not b[i])
        l.append(b)
    return l

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

#NOTE: X is a pivotal node wrt distinct nodes Y and Z
#if X lies on every SHORTEST path between Y and Z and
#X is not equal to Y or Z
#input: graph,x (the node we check for pivotality),y,z (x,y,z are strings)
#output: T if x is a pivotal node wrt y and x
#        F if x is not a pivotal node wrt y and x
#        -1 if x=y or y=z or x=z
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

#NOTE: X is a pivotal node if X is
#pivotal for every pair of distinct vertices Y and Z
#input: a graph and a node x to test for pivotality (str)
#output: T if x is pivotal in general
#        F if x is not pivotal in general
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
def convert_domain_graph_to_string(g):
    n = len(g)
    n2 = n**2 + n
    num = 0
    for v in range(1,n+1):
        for w in g[str(v)]:
            num |= (1<<(n2 - v*n - int(w,10)))
    return str(num)

#input: codomain graph
#output: string version of codomain graph
#this function takes bidirected edges into account
def convert_codomain_graph_to_string(g):
	list_version = bfutils.g2vec(g)
	string = ''
	for item in list_version:
		string = string + str(item)
	return string

#simple loop: directed cycle in which no node is repeated
#input: a graph, node
#output: return a list of all 
#        directed cycles with no node repeats
#        in the graph starting (and obviously ending) from c_node
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

#input: a DOMAIN graph (no bidirected edges)
#output: none. creates a png file of drawing of graph G
def draw_domain_graph(G,name):
	#draw graph
	graph = pydot.Dot(graph_type='digraph')
	#make nodes
	for node in G:
		node_to_add = pydot.Node(node)
		graph.add_node(node_to_add)
	#make edges
	for start in G:
		for end in G[start]:
			if G[start][end] == set([(0, 1)]):   #single directed edge
				edge = pydot.Edge(start, end, color = "black")
				graph.add_edge(edge)
	graph.write_png(name)

#input: a CODOMAIN graph (single AND bidirected edges)
#output: none. creates a png file of drawing of graph G
def draw_codomain_graph(G,name):
	Gcopy = copy.deepcopy(G)
	#remove duplicates
	for u in Gcopy:
		for v in Gcopy[u]:
			if (2,0) in Gcopy[u][v]:
				if v in Gcopy:
					if u in Gcopy[v]: 
						Gcopy[v][u].discard((2,0))
	#draw graph
	graph = pydot.Dot(graph_type='digraph')
	#make nodes
	for node in G:
		node_to_add = pydot.Node(node)
		graph.add_node(node_to_add)
	#make edges
	for start in Gcopy:
		for end in Gcopy[start]:
			if Gcopy[start][end] == set([(0, 1)]):   #single directed edge
				edge = pydot.Edge(start, end, color = "black")
				graph.add_edge(edge)
			elif Gcopy[start][end] == set([(2, 0)]):  #bidirected edge
				edge = pydot.Edge(start, end, color = "red", dir = "both")
				graph.add_edge(edge)
			elif Gcopy[start][end] == set([(0, 1), (2, 0)]):   #single and bidirected edge
				edge1 = pydot.Edge(start, end, color = "red", dir = "both")
				graph.add_edge(edge1)
				edge2 = pydot.Edge(start,end, color = "black")
				graph.add_edge(edge2)
	graph.write_png(name)

#input: the number of nodes
#output: none but creates a zickle file consisting of all the unique 
#unreachable graphs with the designated number of nodes and draws all of them
#warning: non unique reachable graphs zickle file must already be created
def make_unique_urg_and_pics(num_nodes):
    uurgs = determine_unique_unreachable_graphs('rgs_%s.zkl' % num_nodes,num_nodes)
    zkl.save(uurgs,'unique_urgs_%s.zkl' % num_nodes)
    print "Finished importing. Now drawing:"
    d = zkl.load('unique_urgs_%s.zkl' % num_nodes)
    i = 1
    for item in d:
        draw_codomain_graph(item,'pic_unique_urgs_%s_graph_%d.png' % (num_nodes,i))
        print '\n'
        print item
        i = i + 1

#input: two codomain graphs
#output: T if there exists a G and u such that
#X = G^u and Y = G^u+1
#F otherwise
def determine_reachable_combination(X,Y):
    print "tbd"
    reachableList = []
    gts = determine_domain(n)
    for graph in gts:
        reachable_graphs = bfutils.call_undersamples(graph)[1:] 
##################testing area#######################################

#in degree 
#out degree, 
#pivotal nodes 
#centrality
#simple loop lengths
#string notation


#TODO:
#make unique unreachable graphs for 4 nodes see below...too slow for now

#uurgs = determine_unique_unreachable_graphs('rgs_4.zkl',4)
#zkl.save(uurgs,'unique_urgs_4.zkl')
#print "Finished importing. Now drawing:"
#d = zkl.load('unique_rgs_4.zkl')
#i = 1
#for item in d:
#	draw_codomain_graph(item,'pic_unique_rgs_4_graph_%d.png' % i)
#	print '\n'
#	print item
#	i = i + 1




