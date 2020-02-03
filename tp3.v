(** **** Exercise: 3 stars, standard (binary)

 Après la représentation unaire des nombres naturels, nous proposons
 une représentation Binaire plus efficace en traitant un nombre Binaire
 comme une séquence de constructeurs [zero] et [un] (représentant 0 et 1),
 terminée par un [zeroFinal] ou un [unFinal]. En comparaison, dans la
 représentation unaire, un nombre est une séquence de [S] terminée par un [O].

        décimal             binaire                         unaire
           0                   0                              O
           1                   1                            S O
           2                (0 1)                        S (S O)
           3                (1 1)                     S (S (S O))
           4              0 (0 1)                  S (S (S (S O)))
           5              1 (0 1)               S (S (S (S (S O))))
           6              0 (1 1)            S (S (S (S (S (S O)))))
           7              1 (1 1)         S (S (S (S (S (S (S O))))))
           8           0 (0 (0 1))     S (S (S (S (S (S (S (S O)))))))

  Notez que le bit d'ordre inférieur est à gauche et le bit d'ordre supérieur
  est à droite -- à l'opposé de la façon dont les nombres binaires
  sont habituellement écrits. Ce choix facilite leur manipulation.

  Enfin, il peut exister plusieurs représentations binaires d'un entier naturel :
  il suffit d'ajouter des zéros à droite.
**)

(* Préambule *)
(* Quelques lemmes et définitions utiles, certaines donnant lieu à des tactiques standards. 
 * Ces tactiques standards traitent de l'absurdité et de l'égalité. Elle sont à connaître :
 * - exfalso,
 * - f_equal
 * - discriminate.
 * On s'aperçoit que toutes ces tactiques peuvent s'exprimer en utilisant la tactique primitive
 * case, et quelques lemmes pratiques (appliqués avec apply ou refine).
 *)

(* Arguments implicites.
 * Il est possible de déclarer des paramètres entre accolades au lieu de parenthèses.
 * Ces paramètres donnent des arguments implicites : Coq les devine par lui-même.
 * Si on veut utiliser tous les arguments d'une fonction f, écrire l'appel ainsi :
 * - (@f args).
 *)

(* Lors de définitions par cas, il arrive que certains cas soient absurdes.
   On utilise alors la fonction casImpossible. *)   
Definition casImpossible{T : Type}(H : False) : T.
  case H. (* voir le principe récursif False_rect. *)
Defined.

Print False_ind.
Print False_rect.

Print casImpossible.

(* alternative utilisant exfalso et False_rect. *)
Definition casImpossible'{T : Type}(H : False) : T.
    exfalso.
    exact H.
Defined.

Print casImpossible'.

(* Cette notation permet de masquer la preuve de l'absurdité (du Faux). *)
Notation "'Impossible'" := (casImpossible _) : type_scope.

(* Très souvent, l'absurdité vient d'une égalité impossible 
 * entre deux termes de structures différentes. *) 

Ltac egaliteImpossible eg := (apply casImpossible; discriminate eg).

(* discriminate est une tactique élaborée. Elle utilise la préservation 
 * de l'égalité par les fonctions pour déduire le Faux, à partir d'une égalité impossible.
 * La préservation de l'égalité est exploitée par la tactique f_equal.
 *)

Lemma preservationFonctionnelleEgalite :
  forall {A B : Type}{F : A -> B},
  forall x y, x = y -> F x = F y.
Proof.
  intros A B F x y eg.
  case eg.
  reflexivity.
Qed.

(* Plutôt que "case eg", on peut utiliser "rewrite eg".
 *  rewrite est une tactique plus élaborée fondée sur l'égalité et sa décomposition via case.
 *)
Lemma preservationFonctionnelleEgalite' :
  forall {A B : Type}{F : A -> B},
  forall x y, x = y -> F x = F y.
Proof.
  intros A B F x y eg.
  (* rewrite eg. (* équivalent à case (eq_sym eg) 
                    (où eq_sym est le lemme de symmétrie / égalité *) 
   *)
  rewrite <- eg. (* équivalent à case eg *) 
  reflexivity.
Qed.

(* Tactique f_equal := apply preservationFonctionnelleEgalite *)

Ltac egaliteFctn := apply preservationFonctionnelleEgalite.

(* Vers la discrimination :
 * si x = y, (P x) et non (P y), alors on a une contradiction. 
 * On utilise la préservation de l'égalité par un prédicat (une fonction vers Prop).
 *)

Lemma discrimination :
  forall {A : Type},
  forall x y,
    x = y -> (exists (P : A -> Prop), (P x) /\ (P y -> False)) -> False.
Proof.
  intros A x y eg.
  case eg.
  intro H.
  case H as [P [Px abs]].
  apply (abs Px).
Qed.

(* Tactique pour discriminer une égalité fausse :
 * - appliquer discrimination
 * - définir (P n) par : si n vaut x alors True sinon False. 
 * Le test relativement à x se fait par filtrage, sans utiliser l'égalité.
 * eg : x = y
 * discriminant := 
 * (fun n => match n with (filtrage étendu)
           | x => True (x à remplacer par la valeur)
           | _ => False
           end)  
 *)
Ltac discriminer eg discriminant :=
 apply (discrimination _ _ eg); 
 simple refine (ex_intro _ _ _);
 [ exact discriminant
 | simpl; tauto].

Example disc_5_6 : 5 = 6 -> False.
intro eg.
discriminer eg (fun n => match n with 
                         | 5 => True 
                         | _ => False
                         end). 
Qed.

Print disc_5_6. (* Noter que le filtrage est plus élémentaire que dans l'écriture au-dessus. 
                 * Il décrit tous les sous-termes de 5. 
                 *)

(* discriminate produit automatiquement le discriminant. *)

Example disc_5_6' : 5 = 6 -> False.
intro eg.
discriminate eg. 
Qed.

Print disc_5_6'. (* discriminate a effectivement produit automatiquement le discriminant. *)

(* Fin du préambule *)

(* Définition permettant d'obtenir une correspondance bi-univoque *)
Inductive SorteBinaire : Type
  := T1 | N.

(* N ::= 0 | T1 (N = forme normale)
   T1 ::= 1 | 0.T1 | 1 T1 (T1 = se termine par un 1)
 *)
Inductive Binaire : SorteBinaire -> Type :=
  | zeroFinal : Binaire N
  | unFinal : Binaire T1
  | double : Binaire T1 -> Binaire T1
  | successeurDouble : Binaire T1 -> Binaire T1
  | formeNormale : Binaire T1 -> Binaire N.

(** nat comme Binaire forment des algèbres initiales.
  * - nat : signature Nat := (0 : nat), (S : nat -> nat)
  * - Binaire : signature Bin avec deux sortes N et T1
  * - cinq opérations := (OF : Binaire N), (1F : Binaire T1), 
  *    (double : Binaire T1 -> Binaire T1), (successeurDouble: Binaire T1 -> Binaire T1), 
  *    (fn : Binaire T1 -> Binaire N)
  *
  * Propriété importante des algèbres initiales :
  - il existe un unique morphisme d'une algèbre initiale vers une algèbre sur la même signature.
  *
  * Une algèbre est donnée par des ensembles (un par sorte) et des fonctions sur ces ensembles
  * (une par opération de la sorte, en respectant le type).
  *
  * L'algèbre initiale est formée des termes, soit les arbres formés à partir des opérations, 
  * en respectant le typage.
  *  
  * Signature Bin
  * On interprète N par nat et T1 par nat* (nat - 0). Comme nat* est isomorphe à nat,
  * on simplifie : on interprète T1 par nat.
  * (nat/N, nat/T1) est une algèbre sur Bin.
  * Signature Nat
  * Binaire N est une algèbre sur Nat, Binaire T1 est une algèbre sur Nat.
  *
  * La propriété d'initialité permet de relier nat et Binaire.
  *  - si (nat/N, nat/T1) est une algèbre sur Bin, 
  *    alors il existe un unique morphisme BN := (BN N, BN T1) 
  *    sur Bin de Binaire vers (nat/N, nat/T1).
  *  - si (Binaire s) est une algèbre sur Nat, 
  *    alors il existe un unique morphisme (NB s) sur Nat de nat vers (Binaire s).
  *
  * Pour montrer qu'il s'agit d'isomorphismes, il suffit de montrer que 
  * - chaque composante (BN s) est aussi un morphisme sur Nat de (Binaire s) vers nat/s,
  * - (NB N, NB T1) est aussi un morphisme sur Bin de (nat/N, nat/T1) vers Bin.
  * NB o BN est alors un morphisme sur Bin de Binaire vers Binaire : 
  * par unicité, il est égal à l'identité.
  * De même (BN s) o (NB s) est un morphisme sur Nat de nat vers nat : 
  * par unicité, il est égal à l'identité. 
*)

Local Notation "'BO'" := zeroFinal : type_scope.
Local Notation "'I'" := (unFinal) : type_scope.
Local Notation "'O,' x" := (double x) (at level 30, right associativity) : type_scope.
Local Notation "'I,' x" := (successeurDouble x) (at level 30, right associativity) : type_scope.
Local Notation "'B' x" := (formeNormale x) (at level 30, right associativity) : type_scope.

Check (B O,I,O,I).
Check (O,I,O,I).
Check (BO).

(* On cherche à définir les opérations de la signature Bin dans (nat/N, nat/T1) 
 * et celles de la signature Nat dans (Binaire s) (s : sorte). 
 * Rappel
 * Comme il y a deux sortes, on associe deux ensembles, côté nat :
 * - sorte N : nat
 * - sorte T1 : nat pour représenter nat* (nat - 0) (0 pour représenter 1, 1 pour représenter 2, etc.)
 * Attention : bien penser au décalage dans nat/T1.
 *)

(* Cette fonction correspond à la notation nat/s, utilisée en commentaire. *)
Definition natBinaire(e : SorteBinaire) : Type := nat.

(* natBinaire comme algèbre sur B *)

Definition zeroFinalNat : natBinaire N := 0. 

Definition unFinalNat : natBinaire T1 := 0. (* Rappel : décalage
                                             * car représentation de T1 par nat au lieu de nat* *)

(* Fonction qui à n associe (n + 1) * 2 - 1. 
 *   (à cause du décalage)
 * Pour simplifier les calculs, il est préférable d'utiliser seulement 
 * la fonction S (successeur).
 *)
Definition doubleNat : natBinaire T1 -> natBinaire T1. (* +1 -> * 2 -> -1 *) 
Proof.
  intro n.
  induction n.
  - exact 1.
  - exact (S (S IHn)).
Defined.

(* Fonction qui à n associe (n + 1) * 2. 
 *   (à cause du décalage)
 * Pour simplifier les calculs, il est préférable d'utiliser seulement 
 * la fonction S (successeur).
 *)
Definition successeurDoubleNat(n : natBinaire T1) : natBinaire T1. (* -> +1 -> *2  *)
Proof.
  exact (S (doubleNat n)).
Defined.

Definition formeNormaleNat(n : natBinaire T1) : natBinaire N := S n.  (* Rappel : décalage *)

(* (Binaire s) comme algèbre sur Nat *)

(* Interprétation de zéro dans (Binaire N) et (Binaire T1).
 * Prise en compte du décalge.
 *) 
Definition zeroBinaire(s : SorteBinaire) : Binaire s.
Proof.
  case s.
  - exact unFinal.
  - exact zeroFinal.
Defined.

(* interprétation de successeur dans (Binaire N) et (Binaire T1).
 * prise en compte du décalge.
 *) 
Fixpoint successeurBinaire {e : SorteBinaire}(b : Binaire e) : Binaire e.
Proof.
  Show Match Binaire.
  case b as [ | | b' | b' | b'].
  - exact (formeNormale unFinal).
  - exact (double unFinal).
  - exact (successeurDouble b').
  - exact (double (successeurBinaire T1 b')).
  - exact (formeNormale (successeurBinaire T1 b')).
Defined.

(** Conversion de [natBinaire] vers [Binaire] *)
Fixpoint valeurNatEnBinaire(s : SorteBinaire)(n : natBinaire s) : Binaire s.
  (* TODO *)
  admit.
Admitted.

(* La conversion est un morphisme d'algèbre sur Nat.
 * Par définition - simple vérification.
 *) 
Lemma morphismeNat_valeurNatEnBinaire :
  forall s,
  valeurNatEnBinaire s 0 = zeroBinaire s
  /\
  forall n,
    valeurNatEnBinaire s (S n) = successeurBinaire (valeurNatEnBinaire s n). 
Proof.
  (* TODO *)
  admit.
Admitted.

(* La conversion valeurNatEnBinaire est aussi un morphisme d'algèbre sur Bin. 
 * Cinq lemmes, un par opération de la signature.
 *)
Lemma morphismeZeroFinal_valeurNatEnBinaire :
  valeurNatEnBinaire _ zeroFinalNat  = zeroFinal.
  (* TODO *)
  admit.
Admitted.

Lemma morphismeUnFinal_valeurNatEnBinaire :
  valeurNatEnBinaire _ unFinalNat  = unFinal.
  (* TODO *)
  admit.
Admitted.

Lemma morphismeDouble_valeurNatEnBinaire :
  forall n : natBinaire T1,
    valeurNatEnBinaire _ (doubleNat n)  = double (valeurNatEnBinaire _ n).
  (* TODO *)
  admit.
Admitted.

Lemma morphismeSuccesseurDouble_valeurNatEnBinaire :
  forall n : natBinaire T1,
    valeurNatEnBinaire _ (successeurDoubleNat n)  = successeurDouble (valeurNatEnBinaire _ n).
  (* TODO *)
  admit.
Admitted.

Lemma morphismeFormeNormale_valeurNatEnBinaire :
  forall n : natBinaire T1,
    valeurNatEnBinaire _ (formeNormaleNat n)  = formeNormale (valeurNatEnBinaire _ n).
  (* TODO *)
  admit.
Admitted.

(** Conversion de [Binaire] vers [natBinaire] 
 *)

Fixpoint valeurBinaireEnNat{s : SorteBinaire}(b : Binaire s) : natBinaire s.
  (* TODO *)
  admit.
Admitted.

(* La conversion est un morphisme d'algèbre sur Bin.
 * Par définition - simple vérification 
 *)
Lemma morphismeBin_valeurBinaireEnNat :
  valeurBinaireEnNat zeroFinal  = zeroFinalNat
  /\
  valeurBinaireEnNat unFinal  = unFinalNat
  /\
  forall b : Binaire T1,
    valeurBinaireEnNat (double b) = doubleNat (valeurBinaireEnNat b)
  /\
  forall b : Binaire T1,
    valeurBinaireEnNat (successeurDouble b) = successeurDoubleNat (valeurBinaireEnNat b)
  /\
  forall b : Binaire T1,
    valeurBinaireEnNat (formeNormale b) = formeNormaleNat (valeurBinaireEnNat b).
  (* TODO *)
  admit.
Admitted.

(* Chaque composante de la conversion est aussi un morphisme d'algèbre sur Nat. 
 * Deux lemmes, un par opération.
 *)
Lemma morphismeZero_valeurBinaireEnNat :
  forall s, 
      valeurBinaireEnNat (zeroBinaire s)  = 0.
  (* TODO *)
  admit.
Admitted.

Lemma morphismeSuccesseur_valeurBinaireEnNat :
  forall s, forall b : Binaire s,
      valeurBinaireEnNat (successeurBinaire b)  = S (valeurBinaireEnNat b).
  (* TODO *)
  admit.
Admitted.

(* Les isomorphismes *)

(** (valeurBinaireEnNat s) o (valeurNatEnBinaire s) : natBinaire s -> natBinaire s 
 * est un morphisme d'algèbre sur N.
 * Par initialité, c'est l'identité.
 * Démonstration directe ci-dessous.
 *)
Proposition isomorphisme_natBinNat :
  forall s, forall n : natBinaire s, valeurBinaireEnNat (valeurNatEnBinaire s n) = n.
Proof.
  (* TODO *)
  admit.
Admitted.

(** valeurNatEnBinaire o valeurBinaireEnNat : Binaire  -> Binaire  
 * est un morphisme d'algèbre sur B.
 * Par initialité, c'est l'identité.
 * Démonstration directe ci-dessous.
 *)
Proposition isomorphisme_binNatBin :
  forall e, forall b : Binaire e,  (valeurNatEnBinaire e (valeurBinaireEnNat b)) = b.
Proof.
  (* TODO *)
  admit.
Admitted.

(* tests *)

Compute (valeurNatEnBinaire N 17).
Compute (valeurBinaireEnNat (B I,I,O,I)).
Compute (valeurBinaireEnNat (I,I,O,I)).
Compute (valeurNatEnBinaire N (valeurBinaireEnNat (B I,I,O,I))).

(* TODO - Quelques exemples à faire *)

(* 
 * On montre que Binaire N est un ensemble quotient de SuiteBinaire (cf. le TP Binaire).
 * projection : SuiteBinaire -> Binaire N := forme normale
 * représentant : Binaire N -> SuiteBinaire := plongement 
 *)

Inductive SuiteBinaire : Type :=
  | dernierZero : SuiteBinaire
  | dernierUn : SuiteBinaire
  | zero : forall n : SuiteBinaire, SuiteBinaire
  | un : forall n : SuiteBinaire, SuiteBinaire.

Definition representant : forall {s}, (Binaire s) -> SuiteBinaire.
  fix REC 2.
  intros s b.
  case b as [ | | sb | sb | bn].
  - exact dernierZero.
  - exact dernierUn.
  - exact (zero (REC _ sb)).
  - exact (un (REC _ sb)).
  - exact (REC _ bn).
Defined.

(* Pour faciliter l'inversion, on définit la version paramétrée de Bianire. *)
Inductive BinaireP(s : SorteBinaire) : Type :=
  | zeroFinalP : N = s -> BinaireP s
  | unFinalP : T1 = s -> BinaireP s
  | doubleP : T1 = s -> BinaireP T1 -> BinaireP s
  | successeurDoubleP : T1 = s -> BinaireP T1 -> BinaireP s
  | formeNormaleP : N = s -> BinaireP T1 -> BinaireP s.

(* On définit les morphismes entre les deux versions, indexée et paramétrée respectivement. *)
Definition binaireP :
  forall {s}, Binaire s -> BinaireP s.
  fix REC 2.
  intros s b.
  case b as [ | | sb | sb | bn].
  - exact (zeroFinalP N eq_refl).
  - exact (unFinalP T1 eq_refl).
  - exact (doubleP T1 eq_refl (REC _ sb)).
  - exact (successeurDoubleP T1 eq_refl (REC _ sb)).
  - exact (formeNormaleP N eq_refl (REC _ bn)).
Defined.

Print binaireP.

Definition binaireI :
  forall {s}, BinaireP s -> Binaire s.
  fix REC 2.
  intros s b.
  case b as [ eg | eg| eg sb | eg sb | eg bn]; case eg.
  - exact zeroFinal.
  - exact unFinal.
  - exact (double (REC _ sb)).
  - exact (successeurDouble (REC _ sb)).
  - exact (formeNormale (REC _ bn)).
Defined.

Print binaireI.

(* Ces morphismes sont des isomorphismes *)
Lemma isomorphisme_binaireIPI :
  forall s, forall b : Binaire s,
      binaireI (binaireP b) = b.
  (* TODO *)
  admit.
Admitted.

Lemma isomorphisme_binairePIP :
  forall s, forall b : BinaireP s,
      binaireP (binaireI b) = b.
  (* TODO *)
  admit.
Admitted.

(* La projection réalise le calcul de la fome normale, sans zéro inutile à droite.
 * Noter la conversion en BinaireP. Sans celle-ci, l'inversion échoue. 
 *)
Definition projection : SuiteBinaire -> Binaire N.
  fix REC 1.
  intro b.
  case b as [ | | sb | sb].
  - exact BO.
  - exact (B I).
  - case (binaireP (REC sb)) as [ eg| eg | eg sx | eg sx | eg nx];
      try (egaliteImpossible eg).
    + exact BO.
    + pose (y := nx).
      case y as [ eg1| eg1 | eg1 sx1 | eg1 sx1 | eg1 nx1];
        try (egaliteImpossible eg1); exact (B O, (binaireI nx)).
  - case (binaireP (REC sb)) as [ eg| eg | eg sx | eg sx | eg nx];
      try (egaliteImpossible eg).
    + exact (B I).
    + pose (y := nx).
      case y as [ eg1| eg1 | eg1 sx1 | eg1 sx1 | eg1 nx1];
        try (egaliteImpossible eg1); exact (B I, (binaireI nx)).      
Defined.

Print projection.

(* La fonction de normalisation est l'identité ou formeNormale, suivant la sorte. *)
Definition normalisation : forall {s}, Binaire s -> Binaire N.
  intro s.
  case s.
  - intro b.
    exact (formeNormale b).
  - intro b. exact b.
Defined.

Print normalisation.

(* Les deux propositions suivantes établissent la propriété fondamentale d'un ensemble quotient. 
 * Le premier lemme utilise la version paramétrée pour permettre une inversion sans perte 
 * d'informations. 
 *)
Lemma quotient_BinaireP :
  forall e, forall b : BinaireP e,
    projection (representant (binaireI b)) = normalisation (binaireI b).
Proof.
  (* TODO *)
  admit.
Admitted.


Proposition quotient_Binaire :
  forall s, forall b : Binaire s,
    projection (representant b) = normalisation b.
  (* TODO *)
  admit.
Admitted.

Print quotient_Binaire.

(* On déduit la propriété souhaitée pour la sorte N. *)
Corollary quotient_BinaireN :
  forall b : Binaire N,
    projection (representant b) = b.
Proof.
  (* TODO *)
  admit.
Admitted.
