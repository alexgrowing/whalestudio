import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Mathlib

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def KapFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (kap Z)).FG

def KapTrdeg (d : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = d

theorem fnFG_of (h : KapFG Xo c) : FnFG Xo c := by
  intro Z
  classical
  obtain ⟨s, hs⟩ := h Z
  have hfin : (Set.range fun i : FlagVar Dw =>
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X i)).Finite := Set.finite_range _
  refine ⟨s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset, ?_⟩
  set K := IntermediateField.adjoin c.F
    ((s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset : Finset (Om Z)) : Set (Om Z)) with hK
  have hC : ∀ a : kap Z, algebraMap (kap Z) (Om Z) a ∈ K := by
    intro a
    have ha : a ∈ IntermediateField.adjoin c.F (s : Set (kap Z)) := by
      rw [hs]
      exact IntermediateField.mem_top
    have h1 : IsScalarTower.toAlgHom c.F (kap Z) (Om Z) a ∈
        (IntermediateField.adjoin c.F (s : Set (kap Z))).map (IsScalarTower.toAlgHom c.F (kap Z) (Om Z)) :=
      by
        first
          | exact ⟨a, ha, rfl⟩
          | (rw [← SetLike.mem_coe, IntermediateField.coe_map]; exact Set.mem_image_of_mem _ ha)
    rw [IntermediateField.adjoin_map] at h1
    refine IntermediateField.adjoin.mono _ _ _ ?_ h1
    rintro _ ⟨b, hb, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hP : ∀ q : MvPolynomial (FlagVar Dw) (kap Z),
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) q ∈ K := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    next p₁ p₂ h₁ h₂ =>
      rw [map_add]
      exact K.add_mem h₁ h₂
    next p₁ i h₁ =>
      rw [map_mul]
      refine K.mul_mem h₁ (IntermediateField.subset_adjoin c.F _ ?_)
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨i, rfl⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) x
  dsimp only
  rw [IsFractionRing.mk'_eq_div]
  exact K.div_mem (hP p₁) (hP p₂)

private lemma isAlgebraic_frac_lemma {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K) : IsAlgebraic A x := by
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  dsimp only
  have hq : algebraMap A K (q : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  refine ⟨Polynomial.C (q : A) * Polynomial.X - Polynomial.C p, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun f : Polynomial A => f.coeff 1) h0
    simp at h1
    try exact nonZeroDivisors.ne_zero q.2 h1
  · rw [IsFractionRing.mk'_eq_div]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hq, sub_self]

theorem fnTrdeg_of (d : ℕ) (h : KapTrdeg Xo c d) : FnTrdeg Xo c (d + Nat.card (FlagVar Dw)) := by
  intro Z
  haveI h1 : FaithfulSMul (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (kap Z) (MvPolynomial (FlagVar Dw) (kap Z))).injective
  haveI h2 : FaithfulSMul (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z))
  haveI h3 : FaithfulSMul c.F (kap Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap c.F (kap Z)).injective
  haveI h4 : FaithfulSMul (kap Z) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (kap Z) (Om Z)).injective
  have e1 : Algebra.trdeg (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) = Cardinal.mk (FlagVar Dw) := by
    first
      | (rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id])
      | (rw [Algebra.trdeg_mvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq, Cardinal.lift_id])
      | (rw [MvPolynomial.lift_trdeg, Cardinal.lift_id])
      | (rw [Algebra.trdeg_MvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq_cardinalMk, Cardinal.lift_id])
  have e2 : Algebra.trdeg (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) = 0 := by
    unfold Algebra.trdeg
    refine le_antisymm (ciSup_le' fun s => ?_) zero_le
    refine (Cardinal.mk_eq_zero_iff.mpr ⟨fun x => ?_⟩).le
    exact s.2.transcendental x (isAlgebraic_frac_lemma _)
  have hcard : Cardinal.mk (FlagVar Dw) = ((Nat.card (FlagVar Dw) : ℕ) : Cardinal) := by
    first
      | exact Nat.cast_card.symm
      | simp [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have T1 := lift_trdeg_add_eq (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z)
  have T2 := lift_trdeg_add_eq c.F (kap Z) (Om Z)
  simp only [Cardinal.lift_id] at T1 T2
  show Algebra.trdeg c.F (Om Z) = ((d + Nat.card (FlagVar Dw) : ℕ) : Cardinal)
  rw [← T2, h Z, ← T1, e1, e2, add_zero, hcard, Nat.cast_add]

end Formalism.L2.Pj

end
