---- MODULE bfs ----
EXTENDS TLC

CONSTANT Node

VARIABLES edges
VARIABLES nodes

VARIABLES frontier
VARIABLES visited

Init == 
    /\ nodes \in SUBSET Node
    /\ edges \in SUBSET (nodes \X nodes)
    /\ visited = {}
    /\ \E v \in nodes : frontier = {v}

Neighbors(n) == {x \in nodes : <<n,x>> \in edges}

Explore(n) == 
    /\ n \notin visited
    /\ n \in frontier
    /\ visited' = visited \cup {n}
    /\ frontier' = (frontier \ {n}) \cup Neighbors(n)
    /\ UNCHANGED <<nodes, edges>>    

Terminate ==
    /\ frontier = {}
    /\ visited = nodes

Next ==
    \/ \E n \in Node : Explore(n)
    \/ Terminate

Symmetry == Permutations(Node)

L == ~(visited = Node)

====