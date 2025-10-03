
type ('a, 'b) iffT = ('a -> 'b) * ('b -> 'a)

type ('a, 'r) coq_Reflexive = 'a -> 'r

type ('a, 'r) coq_Transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x
