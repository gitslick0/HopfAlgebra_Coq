Require Import VectorSpaces.

Record Algebra (F : Field) : Type := Mk_Algebra {
Algebra_crr   :> (VSpace F);
Alg_mult      : Algebra_crr -> Algebra_crr -> Algebra_crr;
Alg_unit      : F -> Algebra_crr;
Alg_assoc     : forall (a b c : Algebra_crr), Alg_mult (Alg_mult a b) c = Alg_mult a (Alg_mult b c);
Alg_unitality : forall (a: Algebra_crr), Alg_mult (Alg_unit (URing_1 F))  a = a /\ Alg_mult a (Alg_unit (URing_1 F)) = a;
}.


Record BiAlgebra (F : Field) : Type := Mk_Bialgebra {
BiAlgebra_crr :> (Algebra F);
BiAlg_comult  : BiAlgebra_crr -> (prod BiAlgebra_crr BiAlgebra_crr);
BiAlg_counit  : BiAlgebra_crr -> F;
BiAlg_coassoc : forall (a : BiAlgebra_crr), pair ( BiAlg_comult(fst (BiAlg_comult a)) ) (snd (BiAlg_comult a)) = pair ( pair (fst (BiAlg_comult a)) (fst ( BiAlg_comult ( snd ( BiAlg_comult a) ) ) ) ) ( snd ( BiAlg_comult ( snd ( BiAlg_comult a) ) ) );
BiAlg_counitality : forall (a : BiAlgebra_crr), (ScaMult F BiAlgebra_crr) (BiAlg_counit (fst (BiAlg_comult a) ) )  (snd (BiAlg_comult a)) = a /\ (ScaMult F BiAlgebra_crr) (BiAlg_counit (snd (BiAlg_comult a) ) )  (fst (BiAlg_comult a)) = a;

BiAlg_comult_mult : forall (a b : BiAlgebra_crr), BiAlg_comult (Alg_mult F BiAlgebra_crr a b) = pair (Alg_mult F BiAlgebra_crr (fst (BiAlg_comult a)) (fst (BiAlg_comult b))) (Alg_mult F BiAlgebra_crr (snd (BiAlg_comult a)) (snd (BiAlg_comult b)));
BiAlg_comult_unit : BiAlg_comult (Alg_unit F BiAlgebra_crr (URing_1 F)) = pair (Alg_unit F BiAlgebra_crr (URing_1 F)) (Alg_unit F BiAlgebra_crr (URing_1 F));
BiAlg_counit_mult : forall (a b : BiAlgebra_crr), BiAlg_counit (Alg_mult F BiAlgebra_crr a b) = Ring_mop F (BiAlg_counit a) (BiAlg_counit b);
BiAlg_counit_unit : BiAlg_counit (Alg_unit F BiAlgebra_crr (URing_1 F)) = URing_1 F;
}.

Record HopfAlgebra (F : Field) : Type := Mk_HopfAlgebra {
HopfAlgebra_crr   :> (BiAlgebra F);
AP                : HopfAlgebra_crr -> HopfAlgebra_crr;

AP_prop           : forall (a : HopfAlgebra_crr), Alg_mult F HopfAlgebra_crr (AP (fst (BiAlg_comult F HopfAlgebra_crr a))) (snd (BiAlg_comult F HopfAlgebra_crr a)) = ScaMult F HopfAlgebra_crr (BiAlg_counit F HopfAlgebra_crr a)(Alg_unit F HopfAlgebra_crr (URing_1 F))/\Alg_mult F HopfAlgebra_crr ((fst (BiAlg_comult F HopfAlgebra_crr a))) (AP(snd (BiAlg_comult F HopfAlgebra_crr a))) = ScaMult F HopfAlgebra_crr (BiAlg_counit F HopfAlgebra_crr a)(Alg_unit F HopfAlgebra_crr (URing_1 F)); (*/\Alg_mult F HopfAlgebra_crr (fst (BiAlg_comult F HopfAlgebra_crr a)) (AP( snd (BiAlg_comult F HopfAlgebra_crr a))) = a;*)
}.

Definition ConvolutionProduct (F : Field)(H : HopfAlgebra F) : (H -> H) -> (H -> H) -> (H -> H) :=
fun (f g : H -> H) (a : H) => Alg_mult F (HopfAlgebra_crr F H) (f (fst(BiAlg_comult F H a))) (g (snd(BiAlg_comult F H a))).

Print ConvolutionProduct.

Definition EndoConvAlgebra (F : Field) (H:HopfAlgebra F) : Algebra F.

