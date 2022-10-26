Require Import Relations.
Require Import Classes.RelationClasses.
Require Import Setoid.

Record Group : Type := Mk_Group {
  Group_crr :>    Set;
  Group_op  :     Group_crr -> Group_crr -> Group_crr;
  Group_inv :     Group_crr -> Group_crr;
  Group_e   :     Group_crr;

  Group_assoc       : forall (a b c : Group_crr), Group_op (Group_op a b) c = Group_op a (Group_op b c);
  Group_unitality   : forall (a : Group_crr), (Group_op Group_e a = a) /\ (Group_op a Group_e = a);
  Group_inv_prop : forall (a : Group_crr), (Group_op (Group_inv a) a = Group_e)/\ (Group_op a (Group_inv a) = Group_e);
}.

Notation "x <*> y" := (Group_op x y) (at level 50, left associativity).

Record GroupMorph (A B : Group) : Type := Mk_GroupMorph {
  GroupMorph_crr        :>  A->B;
  GroupMorph_unitality  :   GroupMorph_crr (Group_e A) = (Group_e B);
  GroupMorph_mult       :   forall (a b : A), (Group_op B) (GroupMorph_crr a) (GroupMorph_crr b) = GroupMorph_crr (Group_op A a b);
}.

Lemma GroupMorph_inv (A B : Group)(f : GroupMorph A B) : forall (a : A), (Group_inv B (f a)) = f (Group_inv A a).
Proof.
intro a. assert (Group_op B (Group_inv B (f a)) (f a) = Group_op B (f (Group_inv A a)) (f a)).
  - rewrite -> (GroupMorph_mult A B f), -> (proj1 (Group_inv_prop A a)), -> (GroupMorph_unitality A B f), -> (proj1 (Group_inv_prop B (f a))); trivial.
  - assert (((B <*> (B <*> (Group_inv B (f a))) (f a)) (Group_inv B (f a))) = ((B <*> (B <*> (f (Group_inv A a))) (f a) )) (Group_inv B (f a))).
  -- rewrite -> H; trivial.
  -- rewrite <- (proj2 (Group_unitality B (Group_inv B (f a)))), <- (proj2 (Group_unitality B (f (Group_inv A a)))).
     rewrite <- (proj2 (Group_inv_prop B (f a))). rewrite <- (Group_assoc B (Group_inv B (f a)) (f a) (Group_inv B (f a))), <- (Group_assoc B (f (Group_inv A a)) (f a) (Group_inv B (f a))).
     apply H0.
Qed.

Lemma Group_inv_unique (A : Group) : forall (a b : A), (Group_op A a b = Group_e A \/ Group_op A b a = Group_e A) -> b = Group_inv A a.
Proof.
intros a b H. destruct H.
  - rewrite <- (proj1 (Group_unitality A b)), <- (proj1 (Group_inv_prop A a)), -> (Group_assoc A (Group_inv A a) a b), -> H, -> (proj2 (Group_unitality A (Group_inv A a))). trivial.
  - rewrite <- (proj2 (Group_unitality A b)), <- (proj2 (Group_inv_prop A a)), <- (Group_assoc A b a (Group_inv A a)), -> H, (proj1 (Group_unitality A (Group_inv A a))). trivial.
Qed.

Lemma Group_inv_of_mult (A : Group) : forall (a b : A), (Group_inv A (Group_op A a b)) = Group_op A (Group_inv A b) (Group_inv A a).
Proof.
intros a b. assert (H : Group_op A (Group_op A (Group_inv A b) (Group_inv A a))(Group_op A a b) = Group_e A).
  - rewrite -> (Group_assoc A (Group_inv A b) (Group_inv A a) (Group_op A a b)), <- (Group_assoc A (Group_inv A a) a b), -> (proj1 (Group_inv_prop A a)).
    rewrite -> (proj1 (Group_unitality A b)), -> (proj1 (Group_inv_prop A b)). trivial.
  (*- replace H with (Group_op A (Group_op A (Group_inv A b) (Group_inv A a)) (Group_op A a b) = Group_e A \/ Group_op A (Group_op A a b) (Group_op A (Group_inv A b) (Group_inv A a)) = Group_e A).*)
  - rewrite <- (proj2 (Group_unitality A (Group_op A (Group_inv A b)(Group_inv A a)))). rewrite <- (proj2 (Group_inv_prop A (Group_op A a b))). rewrite <- (Group_assoc A (Group_op A (Group_inv A b) (Group_inv A a)) (Group_op A a b) (Group_inv A (Group_op A a b))).
    rewrite -> (Group_assoc A (Group_inv A b) (Group_inv A a) (Group_op A a b)), <- (Group_assoc A (Group_inv A a) a b), -> (proj1 (Group_inv_prop A a )), -> (proj1 (Group_unitality A b)), -> (proj1 (Group_inv_prop A b)).
    rewrite -> (proj1(Group_unitality A (Group_inv A (Group_op A a b)))). trivial.
Qed.

Lemma Group_inv_neutr (A : Group) : Group_e A = Group_inv A (Group_e A).
Proof.
apply (Group_inv_unique A (Group_e A) (Group_e A)). right; rewrite -> (proj1(Group_unitality A (Group_e A))); trivial.
Qed.


Record AbGroup : Type := Mk_AbGroup {
  AbGroup_crr   :>  Group;
  AbGroup_comm  :   forall (a b : AbGroup_crr), (Group_op AbGroup_crr) a b = Group_op AbGroup_crr b a;
}.

Record Ring : Type := Mk_Ring {
  Ring_crr  :>  AbGroup;
  Ring_mop  :   Ring_crr -> Ring_crr -> Ring_crr;
  Ring_assoc:   forall (a b c: Ring_crr), Ring_mop (Ring_mop a b) c = Ring_mop a (Ring_mop b c);
  Ring_dist_l :   forall (a b c: Ring_crr), Ring_mop a (Group_op Ring_crr b c) = Group_op Ring_crr (Ring_mop a b) (Ring_mop a c);
  Ring_dist_r :   forall (a b c: Ring_crr), Ring_mop (Group_op Ring_crr a b) c = Group_op Ring_crr (Ring_mop a c) (Ring_mop b c);
}.

Record RingMorph (A B : Ring) : Type := Mk_RingMorph {
  RingMorph_crr         :> GroupMorph A B;
  RingMorph_mult        : forall (a b : Ring_crr A), Ring_mop B (RingMorph_crr a) (RingMorph_crr b) = RingMorph_crr (Ring_mop A a b);
}.

Record URing: Type := Mk_URing {
  URing_crr :> Ring;
  URing_1 : URing_crr;
  URing_unitality : forall (a : URing_crr), (Ring_mop URing_crr URing_1 a = a)/\(Ring_mop URing_crr a URing_1 = a); 
}.

Record CURing : Type := Mk_CURing {
  CURing_crr :> URing;
  CURing_comm  : forall (a b : CURing_crr), (Ring_mop CURing_crr a b) = (Ring_mop CURing_crr b a);
}.

Record URingMorph (A B : URing) : Type := Mk_URingMorph {
  URingMorph_crr :> RingMorph (URing_crr A) (URing_crr B);
  URingMorph_unitality :  URingMorph_crr (URing_1 A) = URing_1 B;
}.

Record Field : Type := Mk_Field {
  Field_crr :> CURing;
  Field_minv : Field_crr -> Field_crr;
  Field_minv_prop : forall (a : Field_crr), (not (a = URing_1 Field_crr)) -> ((Ring_mop Field_crr (Field_minv a) a = URing_1 Field_crr) /\ (Ring_mop Field_crr a (Field_minv a) = URing_1 Field_crr));
}.

Record FieldMorph (A B : Field) : Type := Mk_FieldMorph {
  FieldMorph_crr      :> URingMorph (Field_crr A) (Field_crr B);
  FieldMorph_multinv  : forall (a : A), FieldMorph_crr (Field_minv A a) = Field_minv B (FieldMorph_crr a);
}.


Record VSpace (F : Field) : Type := Mk_VSpace {
  VSpace_crr    :>  AbGroup;
  ScaMult       : F -> VSpace_crr -> VSpace_crr;
  ScaMult_unitality : forall (a : VSpace_crr), ScaMult (URing_1 F) a = a;
  ScaMult_compmult  : forall (a : VSpace_crr) (l g : F), ScaMult (Ring_mop F l g) a = ScaMult l (ScaMult g a);
  ScaMult_compVadd  : forall (a b : VSpace_crr) (l : F), ScaMult l (Group_op VSpace_crr a b) = Group_op VSpace_crr (ScaMult l a) (ScaMult l b);
  ScaMult_compFadd  : forall (a : VSpace_crr) (l g : F), ScaMult (Group_op F l g) a = Group_op VSpace_crr (ScaMult l a) (ScaMult g a);
}.

Record VSpaceMorph (F : Field) (V W : VSpace F) : Type := Mk_VSpaceMorph {
  VSpaceMorph_crr :> V -> W;
  VSpaceMorph_additive : forall (v1 v2 : V), VSpaceMorph_crr (Group_op V v1 v2) = Group_op W (VSpaceMorph_crr v1) (VSpaceMorph_crr v2);
  VSpaceMorph_scal : forall (v1 : V)(l : F), VSpaceMorph_crr (ScaMult F V l v1) = ScaMult F W l (VSpaceMorph_crr v1)
}.

---------------------------------------------------------------------------------------------------

Axiom fun_ext : forall (A B : Type) (f g : A -> B),
  (forall x : A, f x = g x) -> f = g.

Axiom Group_fun_ext : forall (A B : Group) (f g : GroupMorph A B),
  (forall x : A, f x = g x) -> f = g.

Definition GroupMorph_Id (A : Group) : GroupMorph A A.
refine (Mk_GroupMorph A A (fun (a : A) => a) _ _); trivial; trivial.
Defined.

Definition GroupMorph_Conc (A B C: Group) (f : GroupMorph A B) (g : GroupMorph B C) : GroupMorph A C.
refine (Mk_GroupMorph A C (fun (a:A) => (g (f a))) _ _ ).
  - rewrite -> (GroupMorph_unitality A B f), -> (GroupMorph_unitality B C g); trivial.
  - intros a b; rewrite -> (GroupMorph_mult B C g), -> (GroupMorph_mult A B f); trivial.
Defined.

Record subgroup2 (K : Group) : Type := Mk_Subgroup2 {
      subgroup_crr :>      Group;
      subgroup_mono :      GroupMorph subgroup_crr K;
      subgroup_mono_mon :  forall (L : Group)(f g: GroupMorph L subgroup_crr)(l : L),
             ((GroupMorph_Conc L subgroup_crr K f subgroup_mono) l = (GroupMorph_Conc L subgroup_crr K g subgroup_mono) l) -> (f l = g l);
}.

Definition Identity_Subgroup (K : Group) : subgroup2 K.
refine (Mk_Subgroup2 K K (GroupMorph_Id K) _ ).
intros L f g l. unfold GroupMorph_Conc. compute. trivial.
Defined.

Inductive One_Elem_Set : Set := Star.

Definition Trivial_Group : Group.
refine (Mk_Group One_Elem_Set (fun (x y : One_Elem_Set) => Star) (fun x => Star) Star _ _ _).
- trivial. - intro a; destruct a; split; trivial. - split; trivial.
Defined.

Definition Terminal_Group_Morph (K : Group) : GroupMorph K Trivial_Group.
refine (Mk_GroupMorph K Trivial_Group (fun (x : K) => Star) _ _ ).
- trivial. - intros a b; compute; trivial.
Defined.

Theorem Terminal_Prop_GroupMorph (K : Group) : forall (f : GroupMorph K Trivial_Group), (f = Terminal_Group_Morph K).
- intro f; apply (Group_fun_ext K Trivial_Group f); intro x; destruct (f x); compute; trivial.
Qed. 

Definition GroupMorph_AddInv (A:AbGroup)(B : Group) (f : GroupMorph A B) : GroupMorph A B.
refine (Mk_GroupMorph A B (fun (a:A) => (Group_inv B (f a))) _ _).
  - replace (Group_inv B (f (Group_e A))) with (Group_op B (Group_inv B (f (Group_e A))) (Group_e B)).
  -- rewrite -> (GroupMorph_unitality A B f), -> (proj1 (Group_inv_prop B (Group_e B))); trivial. 
  -- rewrite -> (proj2 (Group_unitality B (Group_inv B (f (Group_e A))))); trivial.
  - intros a b. rewrite -> (GroupMorph_inv A B f a), -> (GroupMorph_inv A B f b). rewrite -> (GroupMorph_mult A B f). rewrite -> (AbGroup_comm A (Group_inv A a) (Group_inv A b)), <- (Group_inv_of_mult A a b), -> (GroupMorph_inv A B f). trivial.
Qed.

Definition GroupMorph_Add (A:Group) (B:AbGroup) (f : GroupMorph A B) (g : GroupMorph A B) : GroupMorph A B.
refine (Mk_GroupMorph A B (fun (a : A) => (Group_op B (f(a)) (g(a)))) _ _).
  - rewrite -> (GroupMorph_unitality A B f), -> (GroupMorph_unitality A B g). rewrite -> (proj1 (Group_unitality B (Group_e B))). trivial.
  - intros a b. rewrite <- (GroupMorph_mult A B f a b), <- (GroupMorph_mult A B g a b). rewrite -> (Group_assoc B (f (a)) (f (b)) (Group_op B (g a) (g b))), <- (Group_assoc B (f b) (g a) (g b)), -> (AbGroup_comm B (f b) (g a)).
    rewrite -> (Group_assoc B (g a) (f b) (g b)), <- (Group_assoc B (f a) (g a) (Group_op B (f b) (g b))). trivial.
Qed.

Definition GroupMorph_Zero (A B: Group) : GroupMorph A B.
refine (Mk_GroupMorph A B (fun (a: A) => (Group_e B)) _ _).
  - trivial.
  - intros a b. rewrite -> (proj1 (Group_unitality B (Group_e B))). trivial.
Qed.

(*---------------------------------------------------------------------------------------------
Making Linear Endomorphisms into a vector space *)

Definition VSpaceMorph_Conc (F : Field)(V W Z : VSpace F)(f : VSpaceMorph F V W)(g : VSpaceMorph F W Z) : VSpaceMorph F V Z.
refine (Mk_VSpaceMorph F V Z (fun (v : V) => g (f v)) _ _).
- intros v1 v2. rewrite -> (VSpaceMorph_additive F V W f), -> (VSpaceMorph_additive F W Z g). trivial.
- intros v1 l. rewrite -> (VSpaceMorph_scal F V W f), -> (VSpaceMorph_scal F W Z g). trivial.
Defined.

Definition VSpaceMorph_Add (F : Field)(V W : VSpace F) (f g : VSpaceMorph F V W) : VSpaceMorph F V W.
refine (Mk_VSpaceMorph F V W (fun (v : V) => Group_op W (f v) (g v)) _ _ ).
- intros v1 v2. rewrite -> (VSpaceMorph_additive F V W f), -> (VSpaceMorph_additive F V W g). Print Group. 
rewrite -> (Group_assoc W (f v1) (f v2) ((W <*> g v1) (g v2))), <- (Group_assoc W (f v2) (g v1) (g v2)). 
rewrite -> (Group_assoc W (f v1) (g v1) ((W <*> f v2) (g v2))), <- (Group_assoc W (g v1) (f v2) (g v2)).
rewrite -> (AbGroup_comm W (f v2) (g v1)). trivial.
- intros v1 l. rewrite -> (VSpaceMorph_scal F V W f), -> (VSpaceMorph_scal F V W g). rewrite <- (ScaMult_compVadd F W (f v1) (g v1) l). trivial.
Defined.

Definition VSpaceMorph_Zero (F : Field)(V W : VSpace F) : VSpaceMorph F V W.
refine (Mk_VSpaceMorph F V W (fun (v : V) => (Group_e W)) _ _).
- intros v1 v2. rewrite -> (proj1 (Group_unitality W (Group_e W))). trivial.
- intros v1 l. rewrite <- (proj1(Group_inv_prop W (Group_e W))) at 2. rewrite <- (Group_inv_neutr W).

Print Mk_Group.

Definition EndoLin_Grp (F : Field)(V W : VSpace F) : Group.
refine (Mk_Group (VSpaceMorph F V W) (VSpaceMorph_Add F V W) _ _ _ _ _).

