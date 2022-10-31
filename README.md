# HopfAlgebra_Coq
Formal Framework for the theory of Hopf algebras in Coq.

So far: 
- We define the algebraic notions of (abelian) groups, (unital, commutative) rings, fields and vector spaces as well as their corresponding morphism classes in VectorSpace.v and proof some rudimentary results such as uniqueness of the inverse element in groups.
- We define the notion of algebra and coalgebras over fields, the notion of a bialgebra and lastly Hopf algebras.
- Next step: Proof that the antipode map of a Hopf algebra is unique. Sketch: Define the convolution product * on the group of linear endomorphisms of some Hopf algebra. This defines a group structure on the Hopf algebra. The antipode map is then the inverse of the identity endomorphism. As inverses are unique, this proofs that the antipode is unique.
