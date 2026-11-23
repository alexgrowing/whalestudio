import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

namespace GlobalTheory.Unf.PartialClass

theorem smooth_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  intro k V hc hd
  have hsm : ∀ φ ∈ V, ContDiff ℝ ∞ φ := by
    refine GlobalTheory.Unf.MatCoef.contDiff_of_partials (fun F => F ∈ V) hc ?_
    intro F hF i
    obtain ⟨φ', hφ', hD⟩ := hd F hF i
    refine ⟨1, fun _ => fun _ => 1, fun _ => φ', fun _ => contDiff_const, fun _ => hφ', ?_⟩
    intro t
    simpa using hD t
  refine ⟨hsm, fun hdec => ?_⟩
  choose φ' hφ' hD using hd

  have hfd : ∀ φ (hφ : φ ∈ V), fderiv ℝ φ = fun x => ∑ i, φ' φ hφ i x •
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
    intro φ hφ
    funext x
    have h := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials k φ (fun i => φ' φ hφ i) (fun i => hc _ (hφ' φ hφ i)) (fun i t => hD φ hφ i t) x
    rw [h.fderiv]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext v
    simp [mul_comm]
  have key : ∀ j : ℕ, ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖iteratedFDeriv ℝ j φ x‖ ≤ C := by
    intro j
    induction j with
    | zero =>
      intro φ hφ N
      obtain ⟨C, hC⟩ := hdec φ hφ N
      exact ⟨C, fun x => by simpa [norm_iteratedFDeriv_zero] using hC x⟩
    | succ j ih =>
      intro φ hφ N
      choose C hC using fun i => ih (φ' φ hφ i) (hφ' φ hφ i) N
      set L : Fin k → ((Fin k → ℝ) →L[ℝ] ℂ) := fun i =>
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ)
      refine ⟨∑ i, ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (L i)‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd φ hφ]
      have hsum : iteratedFDeriv ℝ j (fun x => ∑ i, φ' φ hφ i x • L i) x =
          ∑ i, ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ j (φ' φ hφ i) x) := by
        rw [iteratedFDeriv_fun_sum_apply]
        · refine Finset.sum_congr rfl fun i _ => ?_
          exact iteratedFDeriv_smul_const_apply
            (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).contDiffAt)
        · intro i _
          exact (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).smul contDiff_const).contDiffAt
      rw [hsum]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
        (by positivity)) ?_
      have := hC i x
      nlinarith [norm_nonneg ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)),
        norm_nonneg (iteratedFDeriv ℝ j (φ' φ hφ i) x), pow_nonneg (norm_nonneg x) N]
  intro φ hφ
  refine ⟨{ toFun := φ, smooth' := hsm φ hφ, decay' := fun N j => ?_ }, fun x => rfl⟩
  obtain ⟨C, hC⟩ := key j φ hφ N
  exact ⟨C, hC⟩

end GlobalTheory.Unf.PartialClass
