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

  Inductive Ou (P Q : Prop) : Prop :=
    | ouG : P -> (Ou P Q)
    | ouD : Q -> (Ou P Q).
    

  Inductive Et (P Q : Prop) : Prop :=
    | et : P -> Q -> (Et P Q).
  
  Definition NonP (p: Prop) : Prop := p -> Faux.

  Notation "x \/ y" := (Ou x y) : type_scope.
  Notation "x /\ y" := (Et x y) : type_scope.
  Notation "~ x" := (NonP x) : type_scope.

  Definition ToujoursVrai (n : nat) : Prop.
    exact Vrai.
  Defined.

  Lemma toujoursVrai : forall n, ToujoursVrai n.
  Proof.
    intro n.
    unfold ToujoursVrai.
    apply vrai.
  Qed.


  Lemma n_plus_1_egal_1_plus_n : forall n : nat, n + 1 = 1 + n.
  Proof.
    intro n.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. simpl. reflexivity.
  Qed.

  Lemma distributivite : forall p q r, 
    ((p /\ (q \/ r) -> (p /\ q) \/ (p /\ r)) /\ ((p /\ q) \/ (p /\ r) -> p /\ (q \/ r))). 

  Proof.
    intros P Q R.
    apply et.
    {
      intro C.
      case C as [p ou_qr].
      case ou_qr as [q | r].
      {
        apply ouG.
        apply et.
        assumption.
        assumption.
      }
      {
        apply ouD.
        apply et.
        assumption.
        assumption.
      }
    }
    {
      intro D.
      case D as [et_pq | et_pr].

      {

        case et_pq as [p q].

        apply et.

        assumption.

        apply ouG.

        assumption.

      }

      {

        case et_pr as [p r].

        apply et.

        assumption.

        apply ouD.

        assumption.

      }
    }
    
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
  Qed.

End  Logique.

Module Logique_Indexation.

  Set Warnings "-notation-overridden,-parsing".

  

  Inductive Faux : Prop :=.

  Inductive Vrai : Prop :=

  | vrai.

  (* Définition indexée *)

  Inductive Ou : Prop -> Prop -> Prop :=

  | ouGauche : forall P Q : Prop, P -> Ou P Q

  | ouDroite : forall P Q : Prop, Q -> Ou P Q.

  

  Local Infix "\/" := Ou : type_scope.

  (* Définition indexée *)

  Inductive Et : Prop -> Prop -> Prop :=

  | et : forall P Q : Prop, P -> Q -> Et P Q.

  Local Infix "/\" := Et : type_scope.

  Definition Non(P : Prop) : Prop := P -> Faux.

  Local Notation "~ P" := (Non P) : type_scope.

  Definition ToujoursVrai(n : nat) : Prop.

    exact Vrai.

  Defined.

  Lemma toujoursVrai : forall n, ToujoursVrai n.

  Proof.

    intro n.

    apply vrai.

  Qed.

  (* Equivalence entre la version indexée et celle paramétrée *)

  Lemma eq_etI_etP : forall P Q,

      (P /\ Q) -> (Logique.Et P Q).

  Proof.

    intros P Q EI.

    case EI as [P' Q' p q].

    apply Logique.et.

    exact p.

    exact q.

  Qed.

  Lemma eq_etP_etI : forall P Q,

     (Logique.Et P Q) -> (P /\ Q).

  Proof.

    intros P Q EP.

    case EP as [p q].

    apply et.

    exact p.

    exact q.

  Qed.

  Lemma eq_ouI_ouP : forall P Q,

      (P \/ Q) -> (Logique.Ou P Q).

  Proof.

    intros P Q OI.

    case OI as [P' Q' p | P' Q' q].

    apply Logique.ouG.

    exact p.

    apply Logique.ouD.

    exact q.

  Qed.

  Lemma eq_ouP_ouI : forall P Q,

     (Logique.Ou P Q) -> (P \/ Q).

  Proof.

    intros P Q OP.

    case OP as [p | q].

    apply ouGauche.

    exact p.

    apply ouDroite.

    exact q.

  Qed.

  

  Lemma distributivite : forall P Q R,

      ((P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R))

      /\

      ((P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R))).

  Proof.

    intros P Q R.

    apply et.

    {

      intro C.

      (* case C as [P' QR p qr]. Voici l'effet.

       * Q, R, P', QR : Prop, p : P', qr : QR ⊢ P' /\ Q \/ P' /\ R

       * ----------------------------------------------------------

       * P, Q, R : Prop, C : P /\ (Q \/ R) ⊢ P /\ Q \/ P /\ R

       * Cette tactique ne fonctionne pas, en perdant de l'information.

       * Voici ce que réalise Coq (interprété dans le calcul des séquents, alors que Coq utilise

       * la déduction naturelle.

       * P' QR : Prop, p : P', qr : QR, (P Q R : Prop)[C := et P' QR p qr, P := P', (Q \/ R) := QR]

       * ⊢ (P /\ Q \/ P /\ R)[C := et P' QR p qr, P := P', (Q \/ R) := QR]

       * ----------------------------------------------------------

       * P, Q, R : Prop, C : P /\ (Q \/ R) ⊢ P /\ Q \/ P /\ R

       * 

       * La perte de l'information provient du fait que le remplacement ((Q \/ R) := QR) n'est 

       * pas exploité.

       * Solution :

       * 1. utiliser le système équivalent paramétré.

       *)

      apply eq_etI_etP in C.

      case C as [p qr].

      case qr as [Q' R' q | Q' R' r].

      {

        apply ouGauche.

        apply et.

        assumption.

        assumption.

      }

      {

        apply ouDroite.

        apply et.

        assumption.

        assumption.

      }

    }

    {

      intro D.

      apply eq_ouI_ouP in D.

      case D as [pq | pr].

      {

        case pq as [P' Q' p q].

        apply et.

        assumption.

        apply ouGauche.

        assumption.

      }

      {      

        case pr as [P' R' p r].

        apply et.

        assumption.

        apply ouDroite.

        assumption.

      }

    }

  Qed.

  Print distributivite. (* très proche de Logique.distributivite *)

  Print Logique.distributivite.

  

  Lemma distributivite' : forall P Q R,

      ((P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R))

      /\

      ((P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R))).

  Proof.

    intros P Q R.

    apply et.

    {

      intro C.

      (* case C as [P' QR p qr]. Voici l'effet.

       * Q, R, P', QR : Prop, p : P', qr : QR ⊢ P' /\ Q \/ P' /\ R

       * ----------------------------------------------------------

       * P, Q, R : Prop, C : P /\ (Q \/ R) ⊢ P /\ Q \/ P /\ R

       * Cette tactique ne fonctionne pas, en perdant de l'information.

       * Voici ce que réalise Coq (en utilisant le calcul des séquents, alors que Coq utilise

       * la déduction naturelle).

       * P' QR : Prop, p : P', qr : QR, (P Q R : Prop)[C := et P' QR p qr, P := P', (Q \/ R) := QR]

       * ⊢ (P /\ Q \/ P /\ R)[C := et P' QR p qr, P := P', (Q \/ R) := QR]

       * ----------------------------------------------------------

       * P, Q, R : Prop, C : P /\ (Q \/ R) ⊢ P /\ Q \/ P /\ R

       * 

       * La perte de l'information provient du fait que le remplacement ((Q \/ R) := QR) n'est 

       * pas exploité.

       * Solution :

       * 2. utiliser l'inversion.

       *)

      inversion C as [P' QR' p qr].

      inversion qr as [Q' R' q | Q' R' r].

      {

        apply ouGauche.

        apply et.

        assumption.

        assumption.

      }

      {

        apply ouDroite.

        apply et.

        assumption.

        assumption.

      }

    }

    {

      intro D.

      inversion D as [PQ PR pq | PQ PR pr].

      {

        inversion pq as [P' Q' p q].

        apply et.

        assumption.

        apply ouGauche.

        assumption.

      }

      {      

        inversion pr as [P' R' p r].

        apply et.

        assumption.

        apply ouDroite.

        assumption.

      }

    }

  Qed.

  Print distributivite'. (* preuve complexe, due à l'inversion *)

End  Logique_Indexation.
