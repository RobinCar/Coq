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
 
  | zeroFinal : Binaire

  | unFinal : Binaire

  | zero : forall n : Binaire, Binaire

  | un : forall n : Binaire, Binaire.

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
  case m as [ | | b | b ].
  - exact I.
  - exact (O,I).
  - exact (I, b).
  - exact (O,(successeurBin b)).
Defined.
Print successeurBin.

Fixpoint morphismeNatBinaire (n : nat) : Binaire.
  case n as [ | s].
  - exact O.
  - exact (successeurBin (morphismeNatBinaire s)). 
Defined.
Print morphismeNatBinaire.
(** De [Binaire] vers [nat] *)

Definition zeroFinalNat : nat := 0. 

Definition unFinalNat : nat := 1.

Definition doubleNat (n: nat) : nat.
Proof.
  induction n.
  - exact zeroFinalNat.
  - apply (S (S (IHn))).
Defined. 
Print doubleNat.

Definition successeurDoubleNat (n : nat) : nat.
exact (S (doubleNat n)).
Defined.
Print successeurDoubleNat.

Fixpoint morphismeBinaireNat (m : Binaire) : nat.
Proof.
  case m.
  Show Proof.
  - apply zeroFinalNat.
  - apply unFinalNat.
  - intros. apply (doubleNat (morphismeBinaireNat n)).
  - intros. apply (successeurDoubleNat (morphismeBinaireNat n)).
Defined.


Example example1 : morphismeNatBinaire 10 = O,I,O,I.
reflexivity. Qed.
Example example2 : morphismeBinaireNat (I,I,I) = 7.
reflexivity. Qed.


(** morphismeBinaireNat est un morphisme d'algèbre sur N.*)

Lemma morphismeZero_morphismeBinaireNat :

  morphismeBinaireNat zeroBin = 0.

Proof.
  auto.
Qed.

Lemma morphismeSuccesseur_morphismeBinaireNat :

  forall b, morphismeBinaireNat (successeurBin b) = S (morphismeBinaireNat b).

Proof.
  induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHb. reflexivity.
Qed.
(** morphismeBinaireNat o morphismeNatBinaire : nat -> nat est un morphisme d'algèbre sur N.

 * Par initialité, c'est l'identité.

 *)

Proposition inverseGaucheMorphismeNatBinaire_morphismeBinaireNat :

  forall n, morphismeBinaireNat (morphismeNatBinaire n) = n.

Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite morphismeSuccesseur_morphismeBinaireNat. rewrite IHn. reflexivity.
Qed.
(** Forme normale : pas de zéros à droite, sauf si elle est égale à zéro (zeroFinal) *)

Fixpoint formeNormaleBinaire (b : Binaire) : Binaire.
  case b as [ | | b' | b'].
  - exact O.
  - exact I.
  - case (formeNormaleBinaire b') as [ | | nb' | nb'].
    + exact O.
    + exact (O,I).
    + exact (O,O,nb').
    + exact (O,I,nb').
  - case (formeNormaleBinaire b') as [ | | nb' | nb'].
    + exact I.
    + exact (I,I).
    + exact (I,O,nb').
    + exact (I,I,nb').
Defined. 

Example formeNormale5 : (I,O,I) = formeNormaleBinaire (morphismeNatBinaire 5).
simpl. reflexivity.
Defined.

Example formeNormale5' : (I,O,I) = formeNormaleBinaire (un (zero (un zeroFinal))).

simpl. reflexivity.

Defined.

Compute (formeNormaleBinaire (O,I,O,I,O,O,O,O)).

Compute (formeNormaleBinaire (O,O,O,O,O)).

(** Montrons que morphismeNatBinaire o morphismeBinaireNat : Binaire -> Binaire

 * est équivalent à formeNormaleBinaire.

 * Les lemmes proposés facilitent la démonstration de ce résultat.

 *)

Lemma formeNormale_idempotence :
  forall b, formeNormaleBinaire (formeNormaleBinaire b) = formeNormaleBinaire b.

Proof.
  intro b.
  induction b as [ | | b' | b'].
  1,2: reflexivity.
  - simpl. case (formeNormaleBinaire b') as [ | | nb' | nb'].
    + reflexivity.
    + reflexivity.
    + simpl in IHb'. simpl. rewrite IHb'. reflexivity.
    + simpl in IHb'. simpl. rewrite IHb'. reflexivity.
  - simpl. case (formeNormaleBinaire b') as [ | | nb' | nb'].
    + reflexivity.
    + reflexivity.
    + simpl in IHb'. simpl. rewrite IHb'. reflexivity.
    + simpl in IHb'. simpl. rewrite IHb'. reflexivity. 
Qed.


Lemma successeurBin_commute :

  forall b, successeurBin (formeNormaleBinaire b) = formeNormaleBinaire (successeurBin b).

Proof.
  intros.
  induction b as [ | | b' | b'].
  1,2:reflexivity.
  - simpl. case (formeNormaleBinaire b') as [ | | nb' | nb'].
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl. rewrite <- IHb'. case (formeNormaleBinaire b') as [ | | nb' | nb']. 1-4:reflexivity.
Qed.

Lemma doubleBin :

  forall n, morphismeNatBinaire (doubleNat n) = formeNormaleBinaire (zero (morphismeNatBinaire n)).

Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. 
    rewrite successeurBin_commute. 
    rewrite successeurBin_commute. 
    reflexivity. 
Qed.

Lemma successeurDoubleBin :

  forall n, morphismeNatBinaire (successeurDoubleNat n) = formeNormaleBinaire (un (morphismeNatBinaire n)).

Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite doubleBin.
    rewrite successeurBin_commute.
    rewrite successeurBin_commute.
    rewrite successeurBin_commute.
    reflexivity. 
Qed.

Theorem morphismeBinaireNat_morphismeNatBinaire :

  forall b, morphismeNatBinaire (morphismeBinaireNat b) = formeNormaleBinaire b.

Proof.
  intros.
  induction b.
  1,2:reflexivity.
  - simpl. rewrite doubleBin.
    rewrite IHb. simpl. 
    rewrite formeNormale_idempotence. 
    reflexivity.
  - simpl. rewrite doubleBin.
    rewrite IHb.
    rewrite successeurBin_commute. simpl.
    rewrite formeNormale_idempotence.
    reflexivity.
Qed.