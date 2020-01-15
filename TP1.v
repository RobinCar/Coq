Module SystemeInference.

  (*

   *                    p : Formule  q : Formule

   * ----------------   -------------------------

   *   V : Formule           p ∨ q : Formule

   *)

  Inductive Formule : Type :=

  | vrai : Formule

  | ou : Formule -> Formule -> Formule.

  Local Infix "\/" := ou  : type_scope.

  (*

   *                           (t : T)    (r : Liste T)

   * ------------------       --------------------------

   *  vide T : Liste T          cons T t r : Liste T

   *)

  Inductive Liste(T : Type) : Type := (* paramétrisation par T *)

  | vide : Liste T                    (* constructeur 1 - 

                                       * le paramètre T est le seul paramètre de vide. *) 

  | cons : T -> Liste T -> Liste T.   (* constructeur 2 -

                                       * le paramètre T est le premier paramètre de cons. *)

  Check vide.

  Check cons.

  (* Principes inductifs et récursifs à comprendre. *)

  Print Liste_ind. (* pour raisonner sur les propositions de sorte Prop *)

  Print Liste_rec. (* pour calculer sur les ensembles de sorte Set (petits types *)

  Print Liste_rect. (* pour calculer sur les types de sorte Type (tous les types, y compris Set *)

  Arguments vide {_}. (* Permet de rendre implicite le paramètre T.

                       * Utiliser @vide pour la version explicite. *) 

  Check vide. (* à comparer avec la version où T est encore explicite. *)

  

  Locate "::". (* permet de savoir si la notation existe déjà, et à quoi elle correspond. *)

  Local Notation "x :: y" := (cons _ x y) : type_scope.

  Local Notation "[ ]" := (vide) : type_scope.

  Local Notation "[ x ]" := (cons _ x (vide)) : type_scope.

  Local Notation "[ x ; y ; .. ; z ]" := (cons _ x (cons _ y .. (cons _ z (vide)) ..)) : type_scope.



  Definition l1 := [3 ; 4; 5].

  Print l1.

  Definition l2 := 1 :: [].

  Print l2.

  (*

   * ------------ [Id]

   *    p ⊢ p

   *

   *    Γ ⊢ Δ

   * ------------ [V-G]           ----- [V-D]

   *   V, Γ ⊢ Δ                    ⊢ V

   *

   *

   *                                 Γ ⊢ p, Δ

   *    			                   ---------------- [∨-Dg]

   * p, Γ ⊢ Δ   q, Γ ⊢ Δ          Γ ⊢ (p ∨ q), Δ

   * ------------------- [∨-G]

   *    (p ∨ q), Γ ⊢ Δ                Γ ⊢ q, Δ

   *                              ---------------- [∨-Dd]

   *                               Γ ⊢ (p ∨ q), Δ

   *)

  Inductive ValiditeSequent : Liste Formule -> Liste Formule -> Prop :=

    (* Indexation par deux listes de formules.

     * L'indexation permet une spécialisation de la conclusion dans les règles.

     *)

    | idF : forall p : Formule, ValiditeSequent [p] [p]

    | vraiG : forall G D, ValiditeSequent G D -> ValiditeSequent (vrai :: G) D

    | vraiD : ValiditeSequent [] [vrai]

    | ouG : forall p q G D, ValiditeSequent (p :: G) D

                            -> ValiditeSequent (q :: G) D

                            -> ValiditeSequent ((p \/ q) :: G) D

    | ouDg : forall p q G D, ValiditeSequent G (p :: D)

                            -> ValiditeSequent G ((p \/ q) :: D)

    | ouDd : forall p q G D, ValiditeSequent G (q :: D)

                            -> ValiditeSequent G ((p \/ q) :: D).

  Notation "G |- D" := (ValiditeSequent G D) (at level 90).

  Lemma affaiblissement : forall p q,

      [p] |- [p \/ q].

  Proof.

    intros p q. (* Destruction du forall, ajout des hypothèses (p : nat) et (q : nat) *)
    
    apply ouDg.

    apply idF.

    (* Appliquer les bonnes règles en utilisant les tactiques 

       - apply constructeur.

     *)
  Qed. 

  (* à remplacer par : Qed. Quid est demonstratum. *)

End SystemeInference.

Module Logique.

  Inductive Faux : Prop :=.
  Inductive Vrai : Prop :=
    | vrai.

  Inductive Ou (p q: Prop) : Prop :=
    | ouG : forall (P: Prop) (Q: Prop), p -> (Ou p q)
    | ouD : forall (P: Prop) (Q: Prop), q -> (Ou p q).
    

  Inductive Et : Prop -> Prop -> Prop :=
    | et : forall (P: Prop) (Q: Prop), P -> Q -> (Et P Q).
  
  Definition NonP (p: Prop) : Prop := p -> Faux.

  Notation "x \/ y" := (Ou x y) : type_scope.
  Notation "x /\ y" := (Et x y) : type_scope.
  Notation "~ x" := (NonP x) : type_scope.


  Lemma n_plus_1_egal_1_plus_n : forall n : nat, n + 1 = 1 + n.
  Proof.
    intro n.
    destruct n. 
    auto.
    simpl. auto.
    admit. 
  Admitted.

  Lemma distributivite : forall p q r, 
    ((p /\ (q \/ r) -> (p /\ q) \/ (p /\ r)) /\ ((p /\ q) \/ (p /\ r) -> p /\ (q \/ r))). 

  Proof.
    intros P Q R.
    apply et. right.
  (*
   * Pour appliquer la règle droite de l'implication, 
     - intro H. (H est le nom choisi pour l'hypothèse)
   * Pour appliquer une règle droite décomposant l'opérateur logique C (ou/et) : 
     - apply C.
   * Pour appliquer une règle gauche décomposant l'opérateur logique C (ou/et): 
     - case C as [premisses].
   * On indique dans [premisses] pour chaque règle les noms des variables associées 
   * à chaque prémisse de la règle. Le séparateur est |.
   * Exemples : 
     - Ou -> [p | q] (deux règles, chaque règle ayant une prémisse).
     - Et -> [p q] (une règle, avec deux prémisses).
   *)
   admit.
  Admitted.

End  Logique.
