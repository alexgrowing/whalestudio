import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

open CategoryTheory.Limits in
theorem UpperTheory.Gal.crystallineComparison.corrPull_of :
    CorrPull := by
  intro l S S' Y Y' u f f' h hY T hT
  have Q := IsPullback.of_hasPullback T.p h
  have hw : (pullback.fst T.p h ≫ T.r) ≫ f = (pullback.snd T.p h ≫ f') ≫ u := by
    rw [Category.assoc, hT, ← Category.assoc, pullback.condition, Category.assoc, hY.w,
      Category.assoc]
  have hfin : IsFinite (pullback.snd T.p h) := by
    have := T.fin
    exact MorphismProperty.of_isPullback Q this
  have het : Etale (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) := by
    have hle : Y'.basicOpen (l : Γ(Y', ⊤)) ≤ h ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) :=
      le_of_eq (by rw [Scheme.preimage_basicOpen_top, map_natCast])
    let k := Y'.homOfLE hle ≫ h ∣_ Y.basicOpen (l : Γ(Y, ⊤))
    have e1 : k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ h := by
      simp only [k, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    have A := (isPullback_morphismRestrict (pullback.snd T.p h) (Y'.basicOpen (l : Γ(Y', ⊤)))).flip
    have outer := A.paste_horiz Q
    have R := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have hw2 : ((pullback.snd T.p h ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ pullback.fst T.p h) ≫ T.p
        = (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤)) ≫ k) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      simp only [Category.assoc, pullback.condition, e1, morphismRestrict_ι_assoc]
    have outer' : IsPullback (R.lift _ _ hw2 ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) T.p (k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [R.lift_fst, e1]
      exact outer
    have L := IsPullback.of_right outer' (R.lift_snd _ _ _) R
    exact MorphismProperty.of_isPullback L T.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 →
      ∀ (y : Spec (CommRingCat.of K) ⟶ Y'),
        Nat.card { z // z ≫ pullback.snd T.p h = y } = T.d := by
    intro K _ _ hl y
    rw [← T.deg K hl (y ≫ h)]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ pullback.fst T.p h, by rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨Q.lift z.1 y z.2, Q.lift_snd _ _ _⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      apply Subtype.ext
      apply Q.hom_ext
      · simp
      · simp [z.2]
    · intro z
      apply Subtype.ext
      simp
  refine ⟨⟨pullback T.p h, pullback.snd T.p h, hY.lift _ _ hw, T.d, hfin, het, hdeg⟩,
    pullback.fst T.p h, Q.flip, hY.lift_fst _ _ _, hY.lift_snd _ _ _, rfl⟩
