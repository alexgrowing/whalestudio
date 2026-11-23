import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFieldNumber
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

noncomputable section

theorem CurveFieldNumber.proof (hR1 : RegularityFunctionFieldNumber.Statement) : CurveFieldNumber.Statement := by
  intro K _ ι _ Ω _ y hA hB
  set P := mCoordIdeal y with hPdef
  have : P.IsPrime := hA.2.1.1
  obtain ⟨hF, hN⟩ := hR1 K ι P hA
  let L := FractionRing (MvPolynomial K Ω)

  let j : MRing ι ⧸ P →+* L :=
    (algebraMap (MvPolynomial K Ω) L).comp (RingHom.kerLift (mConeMap y : MRing ι →+* MvPolynomial K Ω))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (MvPolynomial K Ω) L).comp (RingHom.kerLift_injective _)
  let Φ : FractionRing (MRing ι ⧸ P) →+* L := IsFractionRing.lift hj
  let c : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp MvPolynomial.C
  have hΦ : ∀ f, Φ (algebraMap _ _ (Ideal.Quotient.mk P f)) = algebraMap _ L (mConeMap y f) := fun f =>
    (IsFractionRing.lift_algebraMap hj _).trans (congrArg (algebraMap (MvPolynomial K Ω) L)
      (RingHom.kerLift_mk (mConeMap y : MRing ι →+* MvPolynomial K Ω) f))

  have hform : ∀ {g : MRing ι} {a : K → ℕ}, IsMultiHomog g a →
      Φ (algebraMap _ _ (Ideal.Quotient.mk P g)) = c (aeval y g) * algebraMap _ L (∏ k, (X k : MvPolynomial K Ω) ^ a k) := by
    intro g a hg
    rw [hΦ, LowerBoundFree.mConeMap_of_isMultiHomog y hg, map_mul]; rfl
  have hT : ∀ a : K → ℕ, algebraMap (MvPolynomial K Ω) L (∏ k, (X k : MvPolynomial K Ω) ^ a k) ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ (X_ne_zero k))

  have hmem : ∀ {g : MRing ι} {a : K → ℕ}, IsMultiHomog g a → aeval y g = 0 → g ∈ P := by
    intro g a hg h0
    show mConeMap y g = 0
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg, h0, map_zero, zero_mul]

  have heq : (funField P).map Φ = c.range := by
    apply le_antisymm
    · rw [Subring.map_le_iff_le_comap, funField, Subring.closure_le]
      rintro x ⟨u, v, a, hv, hu, hvf, rfl⟩
      have hvP : v ∉ P := fun h => nonZeroDivisors.ne_zero hv ((Ideal.Quotient.eq_zero_iff_mem).2 h)
      have hvy : aeval y v ≠ 0 := fun h => hvP (hmem hvf h)
      refine ⟨aeval y u / aeval y v, ?_⟩
      have h1 := congrArg Φ (IsLocalization.mk'_spec (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩)
      rw [map_mul, hform hvf, hform hu] at h1
      have hcv : c (aeval y v) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hvy
      rw [map_div₀, div_eq_iff hcv]
      exact mul_right_cancel₀ (hT a) (by rw [← h1]; ring)
    · rintro _ ⟨s, rfl⟩
      obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
      have hhP : h ∉ P := fun hP => by
        have : mConeMap y h = 0 := hP
        rw [LowerBoundFree.mConeMap_of_isMultiHomog y hh] at this
        exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective K Ω)).2 hh0)
          (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
      obtain ⟨x, hx⟩ := exists_funField_mul_eq hg hh hhP
      refine ⟨x, x.2, ?_⟩
      have h1 := congrArg Φ hx
      rw [map_mul, hform hh, hform hg, hgs, map_mul] at h1
      have hch : c (aeval y h) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hh0
      exact mul_right_cancel₀ (mul_ne_zero hch (hT d)) (by rw [h1]; ring)

  have hc : Function.Injective c.rangeRestrict := fun a b h => c.injective (congrArg Subtype.val h)
  let e : funField P ≃+* Ω :=
    ((Subring.equivMapOfInjective (funField P) Φ Φ.injective).trans (RingEquiv.subringCongr heq)).trans
      (RingEquiv.ofBijective c.rangeRestrict ⟨hc, c.rangeRestrict_surjective⟩).symm
  exact @NumberField.of_ringEquiv _ _ hF.toField _ e hN

end

end GroundTheory.Heights₂.Heights.Targets
