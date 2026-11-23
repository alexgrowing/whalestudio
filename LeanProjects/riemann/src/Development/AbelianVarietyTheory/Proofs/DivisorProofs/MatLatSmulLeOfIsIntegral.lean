import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

open NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree

namespace GlobalTheory

theorem isIntegral_inv_of_pow_eq_one {K : Type} [Field K] {u : K} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    IsIntegral ℤ u⁻¹ := by
  refine IsIntegral.of_pow hn ?_
  rw [inv_pow, hu, inv_one]
  exact isIntegral_one

theorem matLat_smul_le_of_isIntegral {K : Type} [Field K] [NumberField K] {a b : ℕ} (c : K) (hc : IsIntegral ℤ c)
    (A : Matrix (Fin a) (Fin b) K) (M : Submodule (𝓞 K) (Fin b → K)) :
    Formalism.DivisionValues.matLat (c • A) M ≤ Formalism.DivisionValues.matLat A M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hmem : A.mulVec y ∈ Formalism.DivisionValues.matLat A M := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have h2 := (Formalism.DivisionValues.matLat A M).smul_mem (⟨c, hc⟩ : 𝓞 K) hmem
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  exact h2

theorem finitePlaceBound_inv_rootOfUnity_smul {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}
    {Df : DefSide Bs} (O : FunData K Df) (ze : Bs.Tup → K) (μ : Formalism.PairingDivisionLocalBalance.Pl K → Bs.Tup) (C b : ℝ)
    (hze : ∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) (h : LeafFP O μ C b) :
    LeafFP { O with vmu := fun t => (ze t)⁻¹ • O.vmu t } μ C b := by
  obtain ⟨ha, hb, hc⟩ := h
  refine ⟨fun w => ?_, hb, hc⟩
  obtain ⟨n, hn, hu⟩ := hze (μ w)
  exact le_trans (localization_mono _
    (matLat_smul_le_of_isIntegral _ (isIntegral_inv_of_pow_eq_one hn hu) _ _)) (ha w)

end GlobalTheory
