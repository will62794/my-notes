---- MODULE bfs ----
EXTENDS TLC

CONSTANT Vertex

VARIABLES edges
VARIABLES nodes

VARIABLES explored

VARIABLES frontier

Init == 
    /\ nodes \in SUBSET Vertex
    /\ edges \in SUBSET (nodes \X nodes)
    /\ explored = {}
    /\ \E v \in nodes : frontier = {v}

Neighbors(n) == {x \in nodes : <<n,x>> \in edges}

Next ==
    \E n \in frontier :
        /\ n \notin explored
        /\ frontier # {}
        /\ explored' = explored \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Neighbors(n)
        /\ UNCHANGED <<nodes, edges>>

Symmetry == Permutations(Vertex)

L == ~(explored = Vertex)

====