(** **********************************************************

Matthew Weaver, 2017

 ************************************************************)


(** **********************************************************

Contents : Equivalence of binary products in C/Z to
           pullbacks of pairs of arrows to Z in C

 ************************************************************)

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.

Local Open Scope cat.

(** * Proof that the types of binary products in C/Z and pullbacks of pairs of arrows to Z in C are equivalent *)
Section pullbacks_slice_products_equiv.

  Definition some_pullback (C : category) (Z : C) : UU :=
    ∑ A B (f : A --> Z) (g : B --> Z) , Pullback f g.

  Definition some_binprod (C : category) : UU :=
    ∑ A B , BinProduct C A B.

  Context (C : category).
  Local Notation "C / X" := (slice_cat C X).

  Lemma isPullback_to_isBinProduct {Z : C} {AZ BZ PZ : C / Z} {l : PZ --> AZ} {r : PZ --> BZ} :
     @isPullback _ _ _ _ _ (pr2 AZ) (pr2 BZ) (pr1 l) (pr1 r) (! (pr2 l) @ (pr2 r)) → isBinProduct (C / Z) AZ BZ PZ l r.
  Proof.
    induction AZ as [A f].
    induction BZ as [B g].
    induction PZ as [P h].
    induction l as [l leq].
    induction r as [r req].
    intros isPull [Y i] [j jeq] [k keq]; simpl in *.
    unfold isPullback in isPull. specialize isPull with Y j k.
    use unique_exists.
    + use tpair.
      ++ apply isPull.
         abstract (simpl; now rewrite <- jeq , keq).
      ++ abstract (simpl; now rewrite leq, assoc, (pr1 (pr2 (pr1 (isPull _)))), jeq).
    + abstract (split; apply (eq_mor_slicecat C); simpl;
                [apply (pr1 (pr2 (pr1 (isPull _)))) | apply (pr2 (pr2 (pr1 (isPull _))))]).
    + abstract (now intros q; apply isapropdirprod; apply (has_homsets_slice_precat C)).
    + abstract (intros q [H1 H2]; apply (eq_mor_slicecat C);
                use (maponpaths pr1 ((pr2 (isPull _)) ((pr1 q) ,, (_ ,, _))));
                [apply (maponpaths pr1 H1) | apply (maponpaths pr1 H2)]).
  Defined.

  Lemma slice_isBinProduct_to_isPullback
        {A B Z P : C} {f : A --> Z} {g : B --> Z} {l : P --> A} {r : P --> B} {e : l · f = r · g} :
    isBinProduct (C / Z) (A ,, f) (B ,, g) (P ,, l · f) (l ,, idpath _) (r ,, e) → isPullback (*f g l r*) e.
  Proof.
    intros PisProd Y j k Yeq.
    use unique_exists.
    + exact (pr1 (pr1 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))).
    + abstract (exact (maponpaths pr1 (pr1 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))) ,,
                                  maponpaths pr1 (pr2 (pr2 (pr1 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))))))).
    + abstract (intros x; apply isofhleveldirprod; apply C).
    + intros t teqs.
      use (maponpaths pr1 (maponpaths pr1 (pr2 (PisProd (Y ,, j · f) (j ,, idpath _) (k ,, Yeq))
                                                  ((t ,, (maponpaths (λ x, x · f) (!(pr1 teqs)) @ !(assoc _ _ _) @ maponpaths (λ x, t · x) (idpath _))) ,, _)))).
      abstract (split; apply eq_mor_slicecat; [exact (pr1 teqs) | exact (pr2 teqs)]).
  Defined.

  (** ** equivalence of function taking proof of isPullback to proof of isBinProduct *)
  Lemma isweq_isPullback_to_isBinProduct {Z : C} {AZ BZ PZ : C / Z} {l : PZ --> AZ} {r : PZ --> BZ} :
    isweq (@isPullback_to_isBinProduct Z AZ BZ PZ l r).
  Proof.
    apply isweqimplimpl.
    + induction AZ as [A f].
      induction BZ as [B g].
      induction PZ as [P h].
      induction l as [l leq].
      induction r as [r req].
      simpl in *. induction (! leq).
      assert (H : leq = idpath (l · f)) by apply C.
      intros PisProd.
      apply slice_isBinProduct_to_isPullback; simpl.
      rewrite <- H.
      exact PisProd.
    + apply isaprop_isPullback.
    + apply isaprop_isBinProduct.
  Qed.

  (** ** equivalence of function taking proof of isBinProduct to proof of isPullback *)
  Lemma isweq_slice_isBinProduct_to_isPullback
        {A B Z P : C} {f : A --> Z} {g : B --> Z} {l : P --> A} {r : P --> B} {e : l · f = r · g} :
    isweq (@slice_isBinProduct_to_isPullback A B Z P f g l r e).
  Proof.
    apply isweqimplimpl.
    + intros isPull.
      now apply isPullback_to_isBinProduct.
    + now apply isaprop_isBinProduct.
    + now apply isaprop_isPullback.
  Qed.

  Context (Z : C).

  (** ** pullback_to_slice_binprod is invertible *)
  Lemma pullback_to_slice_binprod_inv {A B : C} {f : A --> Z} {g : B --> Z} (P : Pullback f g) :
    slice_binprod_to_pullback C (pullback_to_slice_binprod C P) = P.
  Proof.
    induction P as [[P [l r]] [Peq PisPull]].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intro.
      apply isofhleveltotal2.
      + apply C.
      + intro.
        apply isaprop_isPullback.
    }
    reflexivity.
  Qed.

  (** ** slice_binprod_to_pullback is invertible *)
  Lemma slice_binprod_to_pullback_inv {AZ BZ : C / Z} (P : BinProduct (C / Z) AZ BZ) :
    pullback_to_slice_binprod C (slice_binprod_to_pullback C P) = P.
  Proof.
    induction AZ as [A f].
    induction BZ as [B g].
    induction P as [[[P h] [[l leq] [r req]]] PisProd].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intro.
      apply isaprop_isBinProduct.
    }
    simpl in *.
    use total2_paths2_f.
    + apply (total2_paths2_f (idpath _)).
      rewrite idpath_transportf.
      exact (!leq).
    + induction (!leq). simpl.
      rewrite idpath_transportf.
      use total2_paths2_f.
    - now apply (eq_mor_slicecat C).
    - rewrite transportf_const.
      now apply (eq_mor_slicecat C).
  Qed.

  (** ** function taking the type of all binary products in C / Z
         to the type of all pullbacks of functions to Z in C *)
  Definition binprod_to_pullback : some_binprod (C / Z) → some_pullback C Z.
  Proof.
    intro P.
    induction P as [AZ BZ].
    induction BZ as [BZ P].
    exact (pr1 AZ ,, pr1 BZ ,, pr2 AZ ,, pr2 BZ ,, slice_binprod_to_pullback C P).
  Defined.

  (** ** function taking the type of all pullbacks of functions to Z in C
         to the type of all binary products in C / Z  *)
  Definition pullback_to_binprod : some_pullback C Z → some_binprod (C / Z).
  Proof.
    intros [A [B [f [g P]]]].
    use ((A ,, f) ,, (B ,, g) ,, pullback_to_slice_binprod C P).
  Defined.

  (** ** binprod_to_pullback is invertible *)
  Lemma binprod_to_pullback_inv (P : some_binprod (C / Z)) :
    pullback_to_binprod (binprod_to_pullback P) = P.
  Proof.
    induction P as [[A f] [[B g] P]].
    unfold pullback_to_binprod , binprod_to_pullback.
    simpl.
    repeat (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    exact (slice_binprod_to_pullback_inv P).
  Qed.

  (** ** pullback_to_binprod is invertible *)
  Lemma pullback_to_binprod_inv (P : some_pullback C Z) :
    binprod_to_pullback (pullback_to_binprod P) = P.
  Proof.
    induction P as [A [B [f [g P]]]].
    unfold binprod_to_pullback , pullback_to_binprod.
    do 4 (apply (total2_paths2_f (idpath _)); rewrite idpath_transportf).
    exact (pullback_to_slice_binprod_inv P).
  Qed.

  Definition isweq_binprod_to_pullback : isweq binprod_to_pullback :=
    isweq_iso _ _ binprod_to_pullback_inv pullback_to_binprod_inv.

  (** ** the equivalence of the types of binary products in C/Z
         and pullbacks of pairs of arrows to Z in C *)
  Definition weq_binprod_to_pullback : weq (some_binprod (C / Z)) (some_pullback C Z) :=
    binprod_to_pullback ,, isweq_binprod_to_pullback.

End pullbacks_slice_products_equiv.
