---- MODULE bfs ----
EXTENDS TLC, Naturals

CONSTANT Node

VARIABLES edges
VARIABLES nodes

VARIABLES frontier
VARIABLES visited

\* Sample graph.
V1 == {1,2,3,4}
E1 == {<<1,2>>, <<1,3>>, <<2,4>>, <<3,4>>}

Init == 
    /\ nodes = Node
    /\ edges \in SUBSET (nodes \X nodes)
    /\ visited = {}
    \* Choose some node as the initial frontier/source.
    /\ \E v \in nodes : frontier = {<<v,0>>}

Neighbors(n) == {x \in nodes : <<n,x>> \in edges}

Explore(n) == 
    /\ n \notin visited
    /\ ~\E x \in frontier : x[1] = n
    /\ visited' = visited \cup {n[1]}
    /\  LET newNeighbors == {x \in Neighbors(n[1]) : x \notin visited'} IN
        frontier' = (frontier \ {n}) \cup {<<b, n[2]+1>> : b \in newNeighbors}
    /\ UNCHANGED <<nodes, edges>>    

Terminate ==
    /\ frontier = {}
    /\ visited = nodes
    /\ UNCHANGED <<nodes, edges, visited, frontier>>

Next ==
    \/ \E n \in frontier : Explore(n)
    \/ Terminate

Symmetry == Permutations(Node)

L == ~(visited = Node)




-------------------------------------------------


\* 
\* Animation stuff.
\* 


\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

DiGraph(V, E, nodeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn], <<>>, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* Graphviz attributes
nodeAttrsFn(n) == [
    label |-> IF n \in visited THEN ToString(n) ELSE ToString(n), 
    style |-> "filled", 
    fillcolor |-> 
        IF n \in visited THEN "lightblue" 
        ELSE IF \E v \in frontier : v[1] = n THEN "lightgray"
        ELSE "white"
]
AnimView == Group(<<DiGraph(nodes,edges,[n \in Node |-> nodeAttrsFn(n)])>>, [i \in {} |-> {}])




====