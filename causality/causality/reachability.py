from __future__ import print_function, unicode_literals, division, absolute_import
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter
import cStringIO
import gzip
from itertools import permutations, product, combinations, chain, izip, repeat, islice
import json
from multiprocessing import Pool, cpu_count
import numpy as np
import os
import shutil
import socket
import subprocess
import sys
from tempfile import NamedTemporaryFile
import time

global _DEBUG


class ConditonalProfile(object):

    """ Conditionally wrap a function in the hotshot profiler """

    def __init__(self, fn):
        self.fn = fn

    def __call__(self, *args, **kw):
        global _DEBUG
        if _DEBUG:
            import hotshot
            import hotshot.stats
            prof = hotshot.Profile("reachability.prof")
            output = prof.runcall(self.fn, *args, **kw)
            prof.close()
            stats = hotshot.stats.load("reachability.prof")
            stats.strip_dirs()
            stats.sort_stats('time', 'calls')
            stats.print_stats(20)
        else:
            output = self.fn(*args, **kw)
        return output


def grouper(n, iterable):
    """ http://stackoverflow.com/a/8991553 """
    it = iter(iterable)
    while True:
        chunk = tuple(islice(it, n))
        if not chunk:
            return
        yield chunk


def generate_partial(args):
    """ Process entry point, write out each graph to a gz file """
    graph_iter, n, outdir = args
    # Write graphs out to gzipped file
    gz_file = NamedTemporaryFile(suffix=".gz", dir=outdir, delete=False)
    gzip_obj = gzip.GzipFile(mode='wb', fileobj=gz_file)
    for subgraphs in graph_iter:
        gzip_obj.write("---\n{}\n...\n".format(json.dumps(subgraphs)))
    gzip_obj.close()
    gz_file.close()


def generate_graphs(graph_iter, graph_count, n, nprocs, outdir):
    """ Determine how to run the graph generator """
    if nprocs != -1:
        # Run locally multiprocess
        if nprocs == 0:
            nprocs = cpu_count()
        pool = Pool(processes=nprocs)
        num_tasks = 10000  # max number of SGE tasks and output files
        chunk_size = max(graph_count / num_tasks, 20000)  # Dont starve workers
        for res in pool.imap(generate_partial, izip(grouper(chunk_size, graph_iter), repeat(n), repeat(outdir))):
            pass
        pool.close()
    else:
        generate_partial((graph_iter, n, outdir))


@ConditonalProfile
def create_domain(n, nprocs, outdir):
    """ Create all possible ground truths with n nodes
        (only single directed edges allowed in domain graphs) """
    vertices = [x + 1 for x in xrange(n)]
    # determine all single directed edges
    single_directed_edge_list = list(product(vertices, vertices))
    # determine all possible graphs that can be formed
    graph_count = len(vertices) ** 2
    allgraphs = chain.from_iterable(combinations(single_directed_edge_list, r) for r in xrange(graph_count + 1))
    generate_graphs(allgraphs, graph_count, n, nprocs, outdir)


@ConditonalProfile
def create_codomain(n, nprocs, outdir):
    """ Create all possible graphs with n many vertices
        (both directed and bidirected edges allowed) """
    vertices = [x + 1 for x in xrange(n)]
    # determine all single directed edges
    single_directed_edge_set = set(product(vertices, vertices))
    # determine all bidirected edges
    bidirected_edge_set = {(k[0], k[1], -1) for k in combinations(vertices, 2)}
    # determine all possible graphs that can be formed
    alledges = single_directed_edge_set | bidirected_edge_set
    graph_count = len(alledges)
    allgraphs = chain.from_iterable(combinations(alledges, r) for r in xrange(graph_count + 1))
    generate_graphs(allgraphs, graph_count, n, nprocs, outdir)


def directed_inc_matrix(G_1, G_u):
    """ Add all directed edges """
    G_u_plus_1 = np.zeros(G_u.shape, dtype=np.int8)
    # get the indicies of the upper triangle
    xs, ys = np.triu_indices(G_u.shape[0])
    for a, b in izip(xs, ys):
        if G_u[a, b] in (1, 5):
            for c in G_1[b].nonzero()[0]:
                if G_1[b, c] in (1, 3):
                    # there exists a path of length u+1 from a to c in G_1
                    if G_u_plus_1[c, a] == 1 or a == c:
                        G_u_plus_1[a, c] = 3
                        G_u_plus_1[c, a] = 3
                    else:
                        G_u_plus_1[a, c] = 1
                        G_u_plus_1[c, a] = 2
        if G_u[a, b] in (2, 6):
            for c in G_1[a].nonzero()[0]:
                if G_1[a, c] in (1, 3):
                    # there exists a path of length u+1 from b to c in G_1
                    if G_u_plus_1[c, b] == 1 or b == c:
                        G_u_plus_1[b, c] = 3
                        G_u_plus_1[c, b] = 3
                    else:
                        G_u_plus_1[b, c] = 1
                        G_u_plus_1[c, b] = 2
        if G_u[a, b] in (3, 7):
            for c in G_1[b].nonzero()[0]:
                if G_1[b, c] in (1, 3):
                    # there exists a path of length u+1 from a to c in G_1
                    if G_u_plus_1[c, a] == 1 or a == c:
                        G_u_plus_1[a, c] = 3
                        G_u_plus_1[c, a] = 3
                    else:
                        G_u_plus_1[a, c] = 1
                        G_u_plus_1[c, a] = 2
            for c in G_1[a].nonzero()[0]:
                if G_1[a, c] in (1, 3):
                    # there exists a path of length u+1 from b to c in G_1
                    if G_u_plus_1[c, b] == 1 or b == c:
                        G_u_plus_1[b, c] = 3
                        G_u_plus_1[c, b] = 3
                    else:
                        G_u_plus_1[b, c] = 1
                        G_u_plus_1[c, b] = 2
    return G_u_plus_1


def bidirected_inc_matrix(G_u_plus_1, G_u):
    """ Add any bidirected edges """
    # get the indicies of the upper triangle
    xs, ys = np.triu_indices(G_u.shape[0])
    # used to flip directed edges to directed edges + a bidirected edge
    add_bi_edge = {0: 4, 1: 5, 2: 6, 3: 7}
    for a, b in izip(xs, ys):
        # transfer old bidirected edges
        if G_u[a, b] in (4, 5, 6, 7):
            # get the current directed value and add the bidirected part, unless it was
            # already a bidirected then do nothing
            G_u_plus_1[a, b] = add_bi_edge.get(G_u_plus_1[a, b], G_u_plus_1[a, b])
            if a != b:
                G_u_plus_1[b, a] = add_bi_edge.get(G_u_plus_1[b, a], G_u_plus_1[b, a])

        # new bidirected edges
        # Collect all indicies
        l = (c for c in G_u[a].nonzero()[0] if G_u[a, c] in (1, 3))
        # Get all permutations of nodes with bidirected edges between them
        for x, y in permutations(l, 2):
            # Add the edge
            G_u_plus_1[x, y] = add_bi_edge.get(G_u_plus_1[x, y], G_u_plus_1[x, y])

    return G_u_plus_1


def directed_inc(G, D):
    G_un = {}
    # directed edges
    for v in D:
        G_un[v] = {}
        for w in D[v]:
            if G[w] and (0, 1) in D[v][w]:
                for e in G[w]:
                    G_un[v][e] = set([(0, 1)])
    return G_un


def bidirected_inc(G, D):
    # bidirected edges
    for w in G:
        # transfer old bidirected edges
        for l in D[w]:
            if (2, 0) in D[w][l]:
                G[w].setdefault(l, set()).add((2, 0))
        # new bidirected edges
        l = [e for e in D[w] if (0, 1) in D[w][e]]
        for pair in permutations(l, 2):
            G[pair[0]].setdefault(pair[1], set()).add((2, 0))
    return G


def increment_u(G_1, G_u, fmt="matrix"):
    if fmt == "matrix":
        G_un = directed_inc_matrix(G_1, G_u)
        G_un = bidirected_inc_matrix(G_un, G_u)
    else:
        G_un = directed_inc(G_1, G_u)
        G_un = bidirected_inc(G_un, G_u)
    return G_un


def call_undersamples(G_1):
    glist = [G_1]
    fmt = "matrix"
    if type(G_1) == dict:
        fmt = "dict"
    while True:
        G = increment_u(G_1, glist[-1], fmt)
        if fmt == "matrix":
            for G_un in glist:
                if (G == G_un).all():
                    # Its already present
                    return glist
        else:
            if G in glist:
                return glist
        glist.append(G)
    return glist


def matrix_to_dict(H):
    """ Convert a graph from matrix format to dictionary format """
    H_dict = {}
    for i in xrange(H.shape[0]):
        H_dict[str(i + 1)] = {}

    def add_directed(a, b):
        """ Add a directed edge """
        H_dict[a].setdefault(b, set()).add((0, 1))

    def add_bidirected(a, b):
        """ Add a bidirected edge """
        H_dict[a].setdefault(b, set()).add((2, 0))
        H_dict[b].setdefault(a, set()).add((2, 0))

    xs, ys = np.triu_indices(H.shape[0])
    for x, y in izip(xs, ys):
        a = str(x + 1)
        b = str(y + 1)
        if H[x, y] == 1:
            # Directed edge from a to b
            add_directed(a, b)
        elif H[x, y] == 2:
            # Directed edge from b to a
            add_directed(b, a)
        elif H[x, y] == 3:
            # Directed edge from a to b and b to a
            add_directed(a, b)
            add_directed(b, a)
        elif H[x, y] == 4:
            # Bidirected edge between a and b
            add_bidirected(a, b)
        elif H[x, y] == 5:
            # Bidirected edge between a and b and directed from a to b
            add_bidirected(a, b)
            add_directed(a, b)
        elif H[x, y] == 6:
            # Bidirected edge between a and b and directed from b to a
            add_bidirected(a, b)
            add_directed(b, a)
        elif H[x, y] == 7:
            # All edges
            add_bidirected(a, b)
            add_directed(a, b)
            add_directed(b, a)

    return H_dict


def tup_to_dict(H, n):
    """ Convert a graph from tuple format to dictionary format

        n is required since the graph may have unreachable nodes that
        are not present in the tuple format.
    """
    H_dict = {}
    for i in xrange(n):
        H_dict[str(i + 1)] = {}
    for edge in H:
        edge = map(str, edge)
        if len(edge) == 2:
            # Directed edge
            H_dict[edge[0]].setdefault(edge[1], set()).add((0, 1))
        else:
            # Bidirected edge, add to both nodes
            H_dict[edge[0]].setdefault(edge[1], set()).add((2, 0))
            H_dict[edge[1]].setdefault(edge[0], set()).add((2, 0))
    return H_dict


def dict_to_matrix(H):
    """ Convert a graph from dictionary format to matrix format

        Cell values to relationship map:
            0 = none
            1 = row -> col
            2 = col -> row
            3 = row -> col AND col -> row
            4 = bi
            5 = row -> col AND bi
            6 = col -> row AND bi
            7 = ALL
    """
    H_matrix = np.zeros([len(H), len(H)], dtype=np.int8)
    for b in H[a]:
        y = int(b) - 1
        val = 0
        if (0, 1) in H[a][b]:
            val = 1
        if (2, 0) in H[a][b]:
            val += 4
        # val can only ever be 1,4 or 5
        # H_matrix[y,x] == 0 means y,x has not been tested yet or there is no path
        if H_matrix[y, x] == 0 and val == 1:
            if x == y:
                # Self loops are defined as 3
                H_matrix[x, y] = 3
                H_matrix[y, x] = 3
            else:
                H_matrix[x, y] = 1
                H_matrix[y, x] = 2
        # H_matrix[y,x] == 1 means there is a path from y,x to x,y
        elif H_matrix[y, x] == 1 and val == 1:
            H_matrix[x, y] = 3
            H_matrix[y, x] = 3
        # H_matrix[y,x] == 0 means y,x has not been tested yet since
        # bidirectionals are marked in both nodes
        elif H_matrix[y, x] == 0 and val == 4:
            H_matrix[x, y] = 4
            H_matrix[y, x] = 4
        # H_matrix[y,x] == 1 means there is a path from y,x to x,y
        elif H_matrix[y, x] == 1 and val == 4:
            H_matrix[x, y] = 6
            H_matrix[y, x] = 5
        # H_matrix[y,x] == 0 means y,x has not been tested yet since
        # bidirectionals are marked in both nodes
        elif H_matrix[y, x] == 0 and val == 5:
            H_matrix[x, y] = 5
            H_matrix[y, x] = 6
        # H_matrix[y,x] == 1 means there is a path from y,x to x,y
        elif H_matrix[y, x] == 1 and val == 5:
            H_matrix[x, y] = 7
            H_matrix[y, x] = 7
        # H_matrix[y,x] == 4 means there is a bidirectional since
        # bidirectionals are marked in both nodes
        elif H_matrix[y, x] == 4 and val == 5:
            H_matrix[x, y] = 5
            H_matrix[y, x] = 6
        # H_matrix[y,x] == 5 means there is a path and bidirectional
        # from y,x to x,y
        elif H_matrix[y, x] == 5 and val == 5:
            H_matrix[x, y] = 7
            H_matrix[y, x] = 7
    return H_matrix


if __name__ == "__main__":
    ''' Run from command line '''
    global _DEBUG
    parser = ArgumentParser(description=
                            'Generates all graphs for a given node size',
                            formatter_class=ArgumentDefaultsHelpFormatter)
    parser.add_argument("-n", type=int, help='Number of nodes in graph')
    parser.add_argument("--profile", help='Print profiling info', action='store_true')
    parser.add_argument('-out', help='Output directory to store results in', type=str, required=True)
    group1 = parser.add_mutually_exclusive_group(required=True)
    group1.add_argument('--domain', help='Generate domain given N', action='store_true')
    group1.add_argument('--codomain', help='Generate co-domain given N', action='store_true')
    # group1.add_argument('-undersamples',help='',action='store_true')
    group2 = parser.add_mutually_exclusive_group(required=False)
    group2.add_argument("-nprocs", type=int, help='Number of processes to spawn, 0 = all', default=-1)
    group2.add_argument("--sge", action='store_true', help='Submit work to Grid Engine', default=False)
    args = parser.parse_args()
    import datetime

    print("time: {}\nargs: {}".format(datetime.datetime.now(), args.__dict__))

    try:
        if os.path.exists(args.out):
            shutil.rmtree(args.out)
        os.makedirs(args.out)
    except OSError, e:
        sys.exit("Cannot create output directory {}: {}".format(args.out, e))

    _DEBUG = False
    if args.profile:
        if args.nprocs == -1:
            _DEBUG = args.profile
        else:
            print("Profiling is not availible in distributed mode.")

    if args.domain:
        if args.n is None:
            sys.exit("You must specify n")

        t0 = time.time()
        create_domain(args.n, args.nprocs, args.out)
        print("Exec Time: {} Seconds".format(time.time() - t0))

    if args.codomain:
        if args.n is None:
            sys.exit("You must specify n")
        t0 = time.time()
        graphs = create_codomain(args.n, args.nprocs, args.out)
        print("Exec Time: {} Seconds".format(time.time() - t0))

    # Combine output files
    try:
        subprocess.check_call("cat {}/tmp* > {}/{}__nodes__{}.gz".format(
                              args.out, args.out, socket.gethostname().split('.')[0], args.n), shell=True)
    except:
        sys.exit("Error collecting results files!")
    try:
        subprocess.check_call("rm {}/tmp*".format(args.out), shell=True)
    except:
        sys.exit("Error removing temporary result files!")
