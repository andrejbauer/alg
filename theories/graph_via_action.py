Theory GraphViaAction.

# A graph may be described by a left action of the monoid M
# of endofunctions from {0,1} to {0,1}. The monoid M has four
# elements: the identity map, the twist map opp, and the
# costants maps src(x) = 0, trg(x) = 1. An action of M on
# a set S is given by maps
#
# id : S -> S
# opp : S -> S
# src : S -> S
# trg : S -> S
#
# Because id is just the identity map we can ignore it.
# Because trg is opp composed with src we don't need to speak about trg.
# So we are left with two unary operations opp and src, which satisfy
# the equations:

Unary src opp.
Axiom: opp(opp(x)) = x.
Axiom: src(src(x)) = src(x).
Axiom: opp(src(x)) = src(x).

# To get a graph from such an action, think of S as the disjoint union
# of vertices and half-edges. The vertices are the fixed-points of src,
# while each half-edge e is connected to the vertex src(e) and to its
# counter-part opp(e). To avoid the situation where a half-edge is its
# own counter-part, we need to require that opp does not have fixed-points
# other than vertices:

Axiom: opp(x) = x -> src(x) = x.
