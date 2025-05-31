import graphviz
import random

edges_acyclic = {
    'A': ['B', 'C'],
    'B': ['D', 'E', 'K'],
    'K': ['Z'],
    'D': ['G'],
    'E': ['Y'],
    'G': ['Q', 'Y'],
    'Q': ['L'],
}

edges_cyclic = {
    'A': ['B', 'C'],
    'B': ['D', 'E', 'K', 'A'],
    'K': ['Z'],
    'D': ['G'],
    'E': ['Y'],
    'G': ['Q', 'Y'],
    'Q': ['L'],
}

def dfs(edges, start, visited=None, shuffle=False):
    frontier = [start]
    visited = []
    frontier_history = [list(frontier)]
    visited_history = [list(visited)]
    while len(frontier) > 0:
        curr = frontier.pop()
        if curr not in visited:
            visited.append(curr)
            visited_history.append(list(visited))
            if curr in edges:
                neighbors = edges[curr]
                for n in neighbors:
                    frontier.append(n)
                # Optionally shuffle frontier randomly to 
                # intentionally break DFS ordering.
                if shuffle:
                    random.shuffle(frontier)
            frontier_history.append(list(frontier))
    print(visited)
    print(frontier_history, len(frontier_history))
    print(visited_history, len(visited_history))
    return (visited, visited_history, frontier_history)


def make_search_graphs(edges, tag, shuffle=False):
    (visited, visited_history, frontier_history) = dfs(edges, 'A', shuffle=shuffle)
    for ind,front in enumerate(frontier_history):
        G = graphviz.Digraph()
        nodes = set()
        for e in edges:
            nodes.add(e)
            for x in edges[e]:
                nodes.add(x)
        for n in nodes:
            G.node(n)

        for n in nodes:
            color = "white"
            if n in front:
                color = "lightgray"
            if n in visited_history[ind]:
                color = "steelblue"
            G.node(n, fillcolor=color, style="filled")
        for n in edges:
            for e in edges[n]:
                G.edge(n, e)
        G.render(f"graphs/{tag}/g{ind}", format="png")

make_search_graphs(edges_acyclic, "acyclic")
make_search_graphs(edges_acyclic, "acyclic_shuffled", shuffle=True)
make_search_graphs(edges_cyclic, "cyclic")


