import sys
import os
scriptpath = "/na/homes/cfreeman/Documents/virtual_test_environment/gunfolds/tools"
sys.path.append(os.path.abspath(scriptpath))
import traversal, bfutils, graphkit,unknownrate,comparison
from itertools import permutations,product,combinations,chain



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
	g = generateEmptyGraph(n)
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
		g = generateEmptyGraph(n)
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
def generateEmptyGraph(n):
	g = {}
	for i in range(n):
		g[str(i+1)] = {} #use str to match sergey's call undersamples func
	return g

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
	


##################testing area#######################################
G = {
'1': {'2': set([(0, 1)])},  
'2': {'2': set([(0, 1)])}, 
}

codomain = [{'1': {}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)])}, '2': {}}, {'1': {}, '2': {'1': set([(0, 1)])}}, {'1': {}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}]
unreachable = [{'1': {}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)])}, '2': {}}, {'1': {}, '2': {'1': set([(0, 1)])}}, {'1': {}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'2': set([(0, 1)])}}, {'1': {'2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}, {'1': {'1': set([(0, 1)]), '2': set([(0, 1), (2, 0)])}, '2': {'1': set([(0, 1)]), '2': set([(0, 1)])}}]
reachable = [{'1': {'2': set([(0, 1)])}, '2': {'2': set([(0, 1)])}}]






#1 = directed edge; 2 = bidirected; 3 = both
#d = {1: set([(0,1)]),
#     2: set([(2,0)]),
#     3: set([(0,1),(2,0)]) }