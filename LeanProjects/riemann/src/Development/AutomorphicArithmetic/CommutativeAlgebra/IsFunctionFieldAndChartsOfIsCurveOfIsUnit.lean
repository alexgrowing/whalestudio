import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartCoverOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeCurveFunctionFieldCompOfNormal

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    (B : Subalgebra k K) : Function.Injective (inc L B) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve {E : Type*} [Field E] {f S T A D : E} {q : ℕ} (hS : S ≠ 0) (hD : D ≠ 0)
    (h : f * (S * D ^ q) = T * A ^ q) : f = T * S⁻¹ * (A * D⁻¹) ^ q := by
  have hDq : D ^ q ≠ 0 := pow_ne_zero _ hD
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination h

theorem UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit :
    Hyps → ∀ (q : ℕ) [NeZero q], ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ Charts k C.functionField q := by
  intro hH q _ k _ _ hq C _ c hc _ hgen
  obtain ⟨hff, n, B, hB, hX⟩ := UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen
  refine ⟨hff, n, B, hB, ?_⟩
  intro L _ _ _ F hF hloc
  obtain ⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩ := hX L
  have hθF : θ F ≠ 0 := (map_ne_zero_iff θ hθ).mpr hF
  have key := UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic
    (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by
      intro y
      obtain ⟨i, m, hm, hw⟩ := hloc' y
      obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm.ne_top
      obtain ⟨s, t, a, b, hs, ht, ha, hb, he⟩ := hloc i M hM
      obtain ⟨ws, hws⟩ := hw s (fun h => hs (hmM h))
      obtain ⟨wt, hwt⟩ := hw t (fun h => ht (hmM h))
      have hinc := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)
      have hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0 := fun z hz =>
        (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)
      have hs0 : s ≠ 0 := fun h => hs (h ▸ M.zero_mem)
      have hA := hne a ha
      have hD := hne b hb
      have hS := hne s hs0
      refine ⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩
      have h1 := congrArg θ he
      simp only [map_mul, map_pow] at h1
      rw [Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]
      exact UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)
  obtain ⟨f, h, hfh⟩ := key
  rw [Units.val_mk0] at hfh
  obtain ⟨a, b, hb, hab⟩ := hfrac ↑h
  have hθb : θ b ≠ 0 := (map_ne_zero_iff θ hθ).mpr hb
  refine ⟨f, a, b, ?_, hb, ?_⟩
  · intro ha
    rw [ha, map_zero] at hab
    exact mul_ne_zero h.ne_zero hθb hab
  · apply hθ
    rw [map_mul, map_mul, map_pow, map_pow, ← hab, hfh]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    ring
