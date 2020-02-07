Require Import List Arith.
Require Extraction.

(** * Tri par inserion certifié

L'objectif est de construire une implémentation certifiée de l'algorithme de tri par insertion.

Nous allons procéder ainsi :
- Spécifier les propriétés recherchées pour un algorithme de tri.
- Définir une implémentation vérifiant ces propriétés.

 *)

(** * Opérateurs de comparaison de nat *)

(* Comparaison par le calcul *)
Locate "=?".
Print Nat.eqb.

Locate "<=?".
Print Nat.leb.

(* Comparaison comme prédicat inductif *)
Locate "<=".
Print le.

(* Les deux approches sont équivalentes *)
Check Nat.leb_spec0.
Print Bool.reflect.

(* Lemme utile pour la suite *)
Lemma leb_swap :
  forall x y, x <=? y = false -> y <=? x = true.
Proof.
  induction x as [ | x' IHx].
  - discriminate.
  - case y as [ | y'].
    + reflexivity.
    + simpl. apply IHx.
Qed.

(* Preuve alternative utilisant la preuve par réflexion *)
Lemma leb_swap_reflect :
  forall x y, x <=? y = false -> y <=? x = true.
Proof.
  intros. case (Nat.leb_spec0 y x) as [Hle | Hlt].
  - reflexivity.
  - exfalso.
    apply Hlt.
    Search (_ <=? _ = false -> _).
    apply leb_complete_conv in H.
    Search (_ < _ -> _ <= _).
    apply Nat.lt_le_incl.
    assumption.
Qed.

(** * Propriétés d'un tri *)

(** Le résultat d'un tri doit être constitué de valeurs croissantes. *)

Inductive sorted : list nat -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall a, sorted(a::nil)
  | sorted2 : forall a b l, a <=? b = true -> sorted (b::l) -> sorted(a::b::l).

Lemma sort_2357 :
  sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
  repeat constructor.
Qed.
(** Le résultat d'un tri doit contenir les mêmes éléments que la liste de départ.
    Il s'agit d'une permutation. *)

(* Nombre d'occurrences de n dans l *)
Fixpoint nb_occ (n : nat) (l : list nat) : nat.
Proof.
  case l as [ | l0 l'].
  - exact 0.
  - case (l0 =? n).
    + exact (S (nb_occ n l')).
    + exact (nb_occ n l').
Defined.

Example ex0 : nb_occ 3 (3 :: 7 :: 3 :: nil) = 2.
Proof.
  reflexivity.
Qed.

(* l' est une permutation de l *)
Definition permutation (l l' : list nat) : Prop :=
  forall n, nb_occ n l = nb_occ n l'.

(* La relation permutation est une relation d'equivalence : *)

Theorem permutation_refl : forall l, permutation l l.
Proof.
  unfold permutation.
  intros.
  transitivity (nb_occ n l).
  - reflexivity.
  - reflexivity. 
Qed.

Theorem permutation_sym : forall l1 l2, permutation l2 l1 -> permutation l1 l2.
Proof.
  unfold permutation.
  intros. symmetry. apply H.
Qed.

Theorem permutation_trans : forall l1 l2 l3, permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Proof.
  unfold permutation.
  intros.
  rewrite H.
  apply H0.
Qed.

(* Autres lemmes utiles : *)

Lemma permutation_cons :
  forall n l l', permutation l l' -> permutation (n :: l) (n :: l').
Proof.
  intros.
  intro x.
  simpl.
  case (n =? x).
  - f_equal. apply H.
  - apply H. 
Qed.

Lemma permutation_transpose :
  forall a b l l', permutation l l' -> permutation (a :: b :: l) (b :: a :: l').
Proof.
  intros.
  unfold permutation.
  intro n. simpl.
  case (a =? n), (b =? n).
  - f_equal. f_equal. apply H.
  - f_equal. apply H.
  - f_equal. apply H.
  - apply H.
Qed.

(** * Implémentation du tri *)

(* Insertion d'un nat dans une liste supposée (informellement) triée *)
Fixpoint insert (n : nat) (l : list nat) : list nat.
  case l as [ | a l'].
  - exact (n::nil).
  - case (n <=? a).
    + exact (n::a::l').
    + exact (a::(insert n l')) .
Defined.

(* insert respecte effectivement l'ordre *)
Lemma insert_sorted :
  forall l x, sorted l -> sorted (insert x l).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl. case (x <=? a) eqn:H.
    + repeat constructor. exact H.
    + repeat constructor. apply leb_swap. exact H.
  - simpl. case (x <=? a) eqn:Ha.
    + repeat constructor. apply Ha. apply H. apply H0.
    + simpl in IHsorted.
      case (x <=? b) eqn:Hb.
      * repeat constructor. apply leb_swap. apply Ha. apply Hb. apply H0.
      * repeat constructor. apply H. apply IHsorted.
Qed.

(* (insert x l) produit une permutation de la liste (x :: l) *)
Lemma insert_permutation :
  forall l x, permutation (x :: l) (insert x l).
Proof.
  intros.
  induction l.
  - simpl. apply permutation_refl.
  - simpl. case (x <=? a).
    + apply permutation_refl.
    + apply (permutation_trans _ (a :: x :: l) _).
      * apply permutation_transpose. apply permutation_refl.
      * apply permutation_cons. apply IHl.
Qed.

(** La fonction de tri *)

(* Le type de retour est une liste accompagnée d'une preuve *)
Locate "{ _ | _ }".
Print sig.

Fixpoint sort (l : list nat) : {ls : list nat | permutation l ls /\ sorted ls}.
  case l as [ | l0 l'].
  - exists nil. split.
    + apply permutation_refl.
    + apply sorted0.
  - case (sort l') as [ls' [Hp Hs]].
    exists (insert l0 ls'). split.
    + apply (permutation_trans _ (l0::ls') _). 
      apply permutation_cons. apply Hp.
      apply insert_permutation.
    + apply insert_sorted. apply Hs.
Defined.

Print sort.

(** * Extraction de code *)

Recursive Extraction sort.

(* On peut utiliser les types primitifs d'OCaml *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant leb => "(<=)".

Recursive Extraction sort.
