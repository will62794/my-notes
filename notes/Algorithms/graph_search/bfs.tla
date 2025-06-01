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



\* \* Animation view definition.
\* c1 == Circle(10, 10, 5, [fill |-> "red"])
\* c2 == Circle(20, 10, 5, [fill |-> "red"])
\* \* ServerIdDomain == 1..Cardinality(Server)
\* RMIdDomain == 1..Cardinality(Server)
\* Spacing == 40
\* XBase == 10
\* logEntryStroke(i,ind) == IF \E c \in committed : c[1] = ind /\ c[2] = log[i][ind] THEN "orange" ELSE "black"
\* logEntry(i, ybase, ind) == Group(<<Rect(20 * ind + 100, ybase, 18, 18, [fill |-> "lightgray", stroke |-> logEntryStroke(i,ind)]), 
\*                                    Text(20 * ind + 105, ybase + 15, ToString(log[i][ind]), ("text-anchor" :>  "start"))>>, [h \in {} |-> {}])
\* logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
\* logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 5)]


\* CrownIcon == "https://www.svgrepo.com/download/274106/crown.svg"

\* CrownElem(rmid, i) == Image(0, i * Spacing - 6, 15, 15, CrownIcon, IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

\* cs == [i \in RMIdDomain |-> 
\*         LET rmid == ToString(RMId[i]) IN
\*         Group(<<
\*             Circle(XBase + 20, i * Spacing, 10, 
\*             [stroke |-> "black", fill |-> 
\*                 IF state[rmid] = Primary 
\*                     THEN "gold" 
\*                 ELSE IF state[rmid] = Secondary THEN "gray" 
\*                 ELSE IF state[rmid] = Secondary THEN "red" ELSE "gray"]), 
\*             CrownElem(rmid,i)>>, [a \in {} |-> {}])]
\* labels == [i \in RMIdDomain |-> 
\*         LET rmid == RMId[i] IN 
\*             Text(XBase + 40, i * Spacing + 5, 
\*             ToString(rmid) \o ", t=" \o ToString(currentTerm[rmid]), \*\o ", " \o ToString(log[rmid]), 
\*             [fill |-> 
\*             IF state[rmid] = Primary 
\*                 THEN "black" 
\*             ELSE IF state[RMId[i]] = Secondary THEN "black" 
\*             ELSE IF state[RMId[i]] = Secondary THEN "red" ELSE "gray"])]
\* AnimView == Group(<<>>, [i \in {} |-> {}])

\* Graphviz attributes
nodeAttrsFn(n) == [label |-> IF n \in visited THEN ToString(n) ELSE ToString(n), style |-> "filled", fillcolor |-> IF n \in visited THEN "lightblue" ELSE "white"]
AnimView == Group(<<DiGraph(nodes,edges,[n \in Node |-> nodeAttrsFn(n)])>>, [i \in {} |-> {}])




====