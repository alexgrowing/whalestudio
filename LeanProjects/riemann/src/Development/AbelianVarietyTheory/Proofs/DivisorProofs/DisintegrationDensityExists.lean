import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralTranslateDetOneCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalUnipotentVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMapContinuousMulDetOneCompactSuppoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalCoefficientCoinvariantEqStatement

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.CuspCutCoef

theorem isCuspFn_cutCoef : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro k _ _ _ _ _ _ N V _ _ π hπ v l hl f hf
  have hsm : IsSmooth π := hπ.1
  have hU : {g : GL (Fin N) k | π g v = v} ∩ {g | ∀ y, l (π g y) = l y} ∈ nhds (1 : GL (Fin N) k) :=
    Filter.inter_mem ((hsm v).mem_nhds (by simp)) (GlobalTheory.CuspCoef.fix_mem_nhds π l hl)
  obtain ⟨γ, hγ, hsub⟩ := GlobalTheory.CentralExponent.exists_cong_subset hU
  set K0 := GlobalTheory.CentralExponent.cong (Fin N) γ hγ with hK0
  have hK0val : ∀ x ∈ K0, ValuativeRel.valuation k (x : Matrix (Fin N) (Fin N) k).det = 1 := by
    intro x hx
    have h1 : x ∈ GlobalTheory.SplitWeil.KO k (Fin N) :=
      KOne_le_KO (mem_KOne.2 fun i j => (hx i j).trans_le hγ)
    obtain ⟨y, rfl⟩ := h1
    have h2 : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k).det = algebraMap 𝒪[k] k (y : Matrix (Fin N) (Fin N) 𝒪[k]).det :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h2]
    exact (Valuation.integer.integers (ValuativeRel.valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit)
  have hbi : ∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g := by
    intro x hx y hy g
    rw [hf, hf]
    have hd : ValuativeRel.valuation k ((x * g * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
        ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
        hK0val x hx, hK0val y hy, one_mul, mul_one]
    rw [hd]
    split_ifs
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hsub y hy).1, (hsub x hx).2]
    · rfl
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_
    have hc : Continuous fun y : GL (Fin N) k => g⁻¹ * y := continuous_const.mul continuous_id
    have : ∀ᶠ y in nhds g, g⁻¹ * y ∈ K0 :=
      hc.continuousAt.preimage_mem_nhds (by
        rw [inv_mul_cancel]
        exact (GlobalTheory.CentralExponent.isOpen_cong γ hγ).mem_nhds K0.one_mem)
    filter_upwards [this] with y hy
    have := hbi 1 K0.one_mem (g⁻¹ * y) hy g
    rwa [one_mul, mul_inv_cancel_left] at this
  obtain ⟨C, hC, hCs⟩ := (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k N V π hπ).2 v l hl
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.T.central_translate_det_one_compact k N C hC
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro hD fun g hg => ?_
    rw [hf]
    split_ifs with h
    · by_contra h0
      obtain ⟨z, hz, c, hc, rfl⟩ := hCs g h0
      exact hg (hDs z hz c hc h)
    · rfl
  refine ⟨hlc, hcs, K0, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, hbi, ?_⟩
  intro a b e ha hb μ hμ u hu g h
  obtain ⟨huc, hum, hud, hup⟩ := GlobalTheory.T.blockUnipotentMap_continuous_mul_det_one_compactSupport k N a b e u hu
  by_cases hg : ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1
  · refine GlobalTheory.T.integral_unipotentRadical_coefficient_coinvariant_eq_zero k N V π hsm a b μ hμ u huc hum (l ∘ₗ π (g * h⁻¹)) (π h v)
      (GlobalTheory.T.cuspidal_unipotent_vanishing k N V π hπ a b e ha hb u hu _) _ (hup f hcs g h) fun X => ?_
    have hd : ValuativeRel.valuation k ((g * (h⁻¹ * u X * h) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 := by
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, hg, one_mul, mul_one]
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one]
    rw [hf, if_pos hd]
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  · have : (fun X => f (g * (h⁻¹ * u X * h))) = fun _ => 0 := by
      funext X
      rw [hf, if_neg]
      intro hd
      apply hg
      simp only [Units.val_mul, Matrix.det_mul, hud X, map_mul, mul_one] at hd
      rwa [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one, mul_one] at hd
    rw [this, integral_zero]

end GlobalTheory.CuspCutCoef
