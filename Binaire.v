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

Inductive Binaire : Type :=

  | zeroFinal : _

  | unFinal : _

  | zero : forall n : Binaire, _

  | un : forall n : Binaire, _.

(** nat comme Binaire forment des algèbres initiales.

  - nat : signature N := (0 : nat), (S : nat -> nat)

  - Binaire (Bin) : signature B := (OF : Bin), (1F : Bin), (zero : Bin -> Bin), (un : Bin -> Bin)

  * Propriété importante des algèbres initiales :

  - il existe un unique morphisme d'une algèbre initiale vers une algèbre sur la même signature.

  * Cette propriété permet de relier nat et Bin.

    - si nat est une algèbre sur B, alors il existe un unique morphisme de Bin vers nat.

    - si Bin est une algèbre sur N, alors il existe un unique morphisme de nat vers Bin.

 *)

Local Notation "'O'" := zeroFinal : type_scope.

Local Notation "'I'" := unFinal : type_scope.

Local Notation "'O,' x" := (zero x) (at level 30, right associativity) : type_scope.

Local Notation "'I,' x" := (un x) (at level 30, right associativity) : type_scope.

Check (O,I,O,I).

(** De [nat] vers [Binaire] *)

Definition zeroBin : Binaire := O.

Fixpoint successeurBin (m : Binaire) : Binaire.

  (* TODO *)

Admitted.

Fixpoint morphismeNatBinaire (n : nat) : Binaire.

  (* TODO *)

Admitted.

(** De [Binaire] vers [nat] *)

Definition zeroFinalNat : nat := 0.

Definition unFinalNat : nat := 1.

Definition doubleNat : nat -> nat.

  (* TODO *)

Admitted.

Definition successeurDoubleNat (n : nat) : nat.

  (* TODO *)

Admitted.

Fixpoint morphismeBinaireNat (m : Binaire) : nat.

  (* TODO *)

Admitted.

(** Ecrire quelques tests pour les morphismes.

 * Un "test unitaire" en Coq est un [Example] spécifique qui

        peut être prouvée avec juste [reflexivity].

 *)

(* TODO *)

(** morphismeBinaireNat est un morphisme d'algèbre sur N.*)

Lemma morphismeZero_morphismeBinaireNat :

  morphismeBinaireNat zeroBin = 0.

Proof.

  (* TODO *)

Admitted.

Lemma morphismeSuccesseur_morphismeBinaireNat :

  forall b, morphismeBinaireNat (successeurBin b) = S (morphismeBinaireNat b).

Proof.

  (* TODO *)

Admitted.

(** morphismeBinaireNat o morphismeNatBinaire : nat -> nat est un morphisme d'algèbre sur N.

 * Par initialité, c'est l'identité.

 *)

Proposition inverseGaucheMorphismeNatBinaire_morphismeBinaireNat :

  forall n, morphismeBinaireNat (morphismeNatBinaire n) = n.

Proof.

  (* TODO *)

Admitted.

(** Forme normale : pas de zéros à droite, sauf si elle est égale à zéro (zeroFinal) *)

Definition formeNormaleBinaire : Binaire -> Binaire.

  (* TODO *)

Admitted.

Example formeNormale5 : (I,O,I) = formeNormaleBinaire (morphismeNatBinaire 5).

  (* simpl. reflexivity. *)

Admitted.

Example formeNormale5' : (I,O,I) = formeNormaleBinaire (un (zero (un zeroFinal))).

  (* simpl. reflexivity. *)

Admitted.

Compute (formeNormaleBinaire (O,I,O,I,O,O,O,O)).

Compute (formeNormaleBinaire (O,O,O,O,O)).

(** Montrons que morphismeNatBinaire o morphismeBinaireNat : Binaire -> Binaire

 * est équivalent à formeNormaleBinaire.

 * Les lemmes proposés facilitent la démonstration de ce résultat.

 *)

Lemma formeNormale_idempotence :

  forall b, formeNormaleBinaire (formeNormaleBinaire b) = formeNormaleBinaire b.

Proof.

  (* TODO *)

Admitted.

Lemma successeurBin_commute :

  forall b, successeurBin (formeNormaleBinaire b) = formeNormaleBinaire (successeurBin b).

Proof.

  (* TODO *)

Admitted.

Lemma doubleBin :

  forall n, morphismeNatBinaire (doubleNat n) = formeNormaleBinaire (zero (morphismeNatBinaire n)).

Proof.

  (* TODO *)

Admitted.

Lemma successeurDoubleBin :

  forall n, morphismeNatBinaire (successeurDoubleNat n) = formeNormaleBinaire (un (morphismeNatBinaire n)).

Proof.

  (* TODO *)

Admitted.

Theorem morphismeBinaireNat_morphismeNatBinaire :

  forall b, morphismeNatBinaire (morphismeBinaireNat b) = formeNormaleBinaire b.

Proof.

  (* TODO *)

Admitted.
