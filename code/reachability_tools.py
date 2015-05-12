import sys
import os
scriptpath = "/na/homes/cfreeman/Documents/virtual_test_environment/gunfolds/tools"
sys.path.append(os.path.abspath(scriptpath))
import traversal, bfutils, graphkit,unknownrate,comparison
from itertools import permutations,product,combinations,chain
from Levenshtein import distance
import numpy as np
from numpy.random import randint
import zickle as zkl
import matplotlib.pyplot as plt




#input: G (the ground truth) 
#output: [G^1,G^2,G^3....G^umax] list of reachable graphs
def determine_reachable_graphs(G):
	return bfutils.call_undersamples(G) #umax = len(gs)

#input: G (the ground truth)
#output: the codomain-list of all possible graphs with the same number of vertices as G (both directed and bidirected edges allowed)
def determine_codomain(G):
	n = 2
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

#input: G(the ground truth)
#output: list of unreachable graphs
def determine_unreachable_graphs(G):
	codomainList = determine_codomain(G)
	reachableList = determine_reachable_graphs(G)
	return [i for i in codomainList if i not in reachableList]

#input: G
#output: cardinality of the codomain 
def determine_codomain_cardinality(G):
	n = len(G)
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
#output: a dictionary where key = vertex and value =   in degree
def determine_in_degrees(G):
	in_degree_dict = {}
	for i in range(len(G)):
		in_degree_dict[str(i+1)] = 0
	for outerkey in G.keys():
		print "\n"
		print "from:",outerkey
		for innerkey in G[outerkey].keys():
			print "to:",innerkey
			print G[outerkey][innerkey]
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
	all_reachable_graphs = determine_reachable_graphs(G)
	for graph in all_reachable_graphs:
		distances.append(determine_edit_distance(graph,H))
	distancesnp = np.array(distances)
	indices_of_nearest_graphs = np.where(distancesnp == distancesnp.min())
	return [all_reachable_graphs[index] for index in indices_of_nearest_graphs]


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


#input: two graphs G1 and G2
#ouput: the distance between the two graphs
def determine_edit_distance(G1,G2):
	G1str = str(graph2str(G1))
	G2str = str(graph2str(G2))
	print distance(G1str,G2str)
	return distance(G1str,G2str)



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
	
#input: m = number of graphs desired, n = number of nodes per graph
#output: a list of m many random graphs each with n nodes (no bidirected edges allowed)
def generate_random_graphs(m,n):
	random_graphs = []
	for i in range(m):
		g = generate_Empty_Graph(n)
		edges_to_add = randint(low=1,high=n**2)
		for k in range(edges_to_add):
			from_vertex = randint(low=1,high=n)
			to_vertex = randint(low=1,high=n)
			e = (from_vertex,to_vertex)
			g[str(e[0])][str(e[1])] =  set([(0,1)])
		random_graphs.append(g)
	return random_graphs

#input: reachable graphs and unreachable graphs (typically from zickle files)
#output:a plot where x axis is degree size, y axis is frequency
def generate_in_degree_plot(reachable_graphs,unreachable_graphs):

	#todo: make alldegrees
	#alldegrees[0] = frequencies of degree 0
	#alldegrees[1] = frequencies of degree 1
	#...
	#alldegrees[n] = frequencies of degree n

	#alldegrees[0][0] = frequencies of degree 0 for unreachable graphs
	#alldegrees[0][1] = frequencies of degree 0 for reachable graphs


	mycolor = [(0.9769448735268946, 0.6468696110452877, 0.2151452804329661), (0.37645505989354233, 0.6875228836084111, 0.30496111115768654)]

	#degree 0
	bp = bar(alldegrees[0],positions[1,2],color = mycolor)

	#degree 1
	bp = bar(alldegrees[1],positions[4,5],color = mycolor)

	#degree 2
	bp = bar(alldegrees[2],positions[7,8],color = mycolor)

	#degree 3
	bp = bar(alldegrees[3],positions[10,11],color = mycolor)

	#degree 4
	bp = bar(alldegrees[4],positions[12,13],color = mycolor)

	#degree 5
	bp = bar(alldegrees[5],positions[15,16],color = mycolor)

	#degree 6
	bp = bar(alldegrees[6],positions[18,19],color = mycolor)

	# set axes limits and labels
	xlim(0,20)
	ax.set_xticklabels(['0', '1', '2','3','4','5','6'])
	ax.set_xticks([1.5,4.5,7.5,10.5,12.5,15.5,18.5])
	#legend
	u2 = mlines.Line2D([], [], color=color[0], marker='s',
	                          markersize=15, markeredgewidth = 1,label='u = 2')
	u3 = mlines.Line2D([], [], color=color[1], markeredgewidth = 1,marker='s',
	                          markersize=15, label='u = 3')
	
	plt.legend(handles=[u2,u3],numpoints = 1,loc = 4)


	plt.xlabel('degree')
	plt.ylabel('frequency')
	plt.title('n = 5, number of graphs = 100' ,multialignment='center')
	plt.show()

#todo later: more graph properties to examine

##################testing area#######################################
G = {
'1': {'2': set([(0, 1)])},  
'2': {'2': set([(0, 1)])}, 
}

codomain = [{'1': {}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)])}, '2': {}}, {'1': {}, '2': {'1': set([(0, 1)])}}, {'1': {}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}]
unreachable = [{'1': {}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)])}, '2': {}}, {'1': {}, '2': {'1': set([(0, 1)])}}, {'1': {}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}]
reachable = [{'1': {'2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}]


#gts[i] = the ith ground truth
#reachable_graphs[i] =  a list of all the reachable graphs formed from gts[i]

gts = zkl.load('100_random_5_node_graphs')
reachable_graphs = zkl.load('reachable_graphs')
unreachable_graphs = zkl.load('unreachable_graphs')