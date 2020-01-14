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

    (* Appliquer les bonnes règles en utilisant les tactiques 

       - apply constructeur.

     *)

    admit.

  Admitted. 

  (* à remplacer par : Qed. Quid est demonstratum. *)

End SystemeInference.

Module Logique.

(* à compléter. *)

End  Logique.
