from __future__ import print_function, unicode_literals, division, absolute_import
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter
import cStringIO
import gzip
from itertools import permutations, product, combinations, chain, izip, repeat, islice
import json
from multiprocessing import Pool, cpu_count
import os
import shutil
import sys
from tempfile import NamedTemporaryFile
import time

global _DEBUG


def handler(obj):
    """ Handle encoding set objects in json """
    if type(obj) == set:
        return list(obj)
    else:
        raise TypeError, 'Object of type {0} with value of {1} is not JSON serializable'.format(type(obj), repr(obj))


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


def generate_empty_graph(n):
    """ input: number of vertices
        ouput: empty graph dictionary for n vertices """
    g = {}
    for i in xrange(n):
        g[str(i + 1)] = {}  # use str to match sergey's call undersamples func
    return g


def grouper(n, iterable):
    """ http://stackoverflow.com/a/8991553 """
    it = iter(iterable)
    while True:
        chunk = tuple(islice(it, n))
        if not chunk:
            return
        yield chunk


def generate_partial(args):
    """ Process entry point, converts a subset of graphs to dictionary form """
    graph_iter, n, outdir = args
    # Write graphs out to gzipped file
    gz_file = NamedTemporaryFile(suffix=".gz", dir=outdir, delete=False)
    gzip_obj = gzip.GzipFile(mode='wb', fileobj=gz_file)
    for subgraphs in graph_iter:
        gzip_obj.write("---\n{}\n...\n".format(subgraphs))
    gzip_obj.close()
    gz_file.close()


@ConditonalProfile
def create_domain(n, nprocs, outdir):
    """ input: number of vertices
        output: list of all possible ground truths with n nodes
        (only single directed edges allowed in domain graphs) """
    vertices = [x + 1 for x in xrange(n)]
    # determine all single directed edges
    single_directed_edge_list = list(product(vertices, vertices))
    # determine all possible graphs that can be formed
    graph_count = len(vertices) ** 2
    allgraphs = chain.from_iterable(combinations(single_directed_edge_list, r) for r in xrange(graph_count + 1))
    if nprocs != -1:
        # Run locally multiprocess
        if nprocs == 0:
            nprocs = cpu_count()
        pool = Pool(processes=nprocs)
        num_tasks = 10000  # max number of SGE tasks and output files
        chunk_size = max(graph_count / num_tasks, 20000)  # Dont starve workers
        for res in pool.imap(generate_partial, izip(grouper(chunk_size, allgraphs), repeat(n), repeat(outdir))):
            pass
        pool.close()
    else:
        generate_partial((allgraphs, n, outdir))



@ConditonalProfile
def create_codomain(n, nprocs, outdir):
    """ input: number of vertices
        output: the codomain-list of all possible graphs with n many vertices
        (both directed and bidirected edges allowed)
        this function is sloooooowww """
    vertices = [x + 1 for x in xrange(n)]
    # determine all single directed edges
    single_directed_edge_list = list(product(vertices, vertices))
    # determine all bidirected edges
    bidirected_edge_list_0 = []
    for k in list(combinations(vertices, 2)):
        bidirected_edge_list_0.append((k[0], k[1], 'bidirected'))  # make these distinct from single direct edges
    # determine all possible graphs that can be formed
    single_directed_edge_set = set(single_directed_edge_list)
    bidirected_edge_set = set(bidirected_edge_list_0)
    alledges = single_directed_edge_set | bidirected_edge_set
    allgraphs = chain.from_iterable(combinations(alledges, r) for r in xrange(len(alledges) + 1))
    # now to convert to dictionary form
    g = generate_empty_graph(n)  # so there can exist nodes that are empty
    glist = []
    for i in allgraphs:
        for e in i:
            e = map(str,e)
            if len(e) == 2:
                g[e[0]][e[1]] = set([(0, 1)])
            else:  # len(e) ==3
                g[e[0]][e[1]] = set([(2, 0)])
        glist.append(g)
        g = generate_empty_graph(n)
    return glist


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


def increment_u(G_star, G_u):
    # directed edges
    G_un = directed_inc(G_star, G_u)
    # bidirected edges
    G_un = bidirected_inc(G_un, G_u)
    return G_un


@ConditonalProfile
def call_undersamples(G_star):
    glist = [G_star]
    while True:
        g = increment_u(G_star, glist[-1])
        if g in glist:
            return glist
        glist.append(g)
    return glist


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
