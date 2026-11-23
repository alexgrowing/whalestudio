import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem slash_sub_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ),
    (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n)
      =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro M Γ k f hM hΓ hf x
  haveI : NeZero M := ⟨hM.ne'⟩
  have hg : IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    refine ⟨fun γ hγ => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · have h1 : x * γ * x⁻¹ ∈ Γ := hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ x)
      rw [← SlashAction.slash_mul, show x * γ = (x * γ * x⁻¹) * x by group]
      exact hf.slash_mul h1 x
    · rw [← SlashAction.slash_mul]; exact hf.2.2 _
  have hper : (M : ℝ) ∈ ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma]; exact AddSubgroup.mem_zmultiples _
  have hperiodic : Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex hg.toMF hper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum := hasSum_qExpansion hMpos hperiodic hg.2.1 (hf.2.2 x)
  have ha := analyticAt_cuspFunction_zero hMpos hperiodic hg.2.1 (hf.2.2 x)
  have hps := hasFPowerSeriesOnBall_cuspFunction hMpos ha hsum
  have hbig := (hps.hasFPowerSeriesAt.isBigO_sub_partialSum_pow M).comp_tendsto (qParam_tendsto_atImInfty hMpos)
  refine hbig.congr (fun τ => ?_) (fun τ => ?_)
  · simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, co]
    rw [eq_cuspFunction τ (by positivity) hperiodic]
  · simp only [Function.comp_apply, Function.Periodic.norm_qParam, coe_im]
    rw [← Real.exp_nat_mul]; congr 1; field_simp

end GlobalTheory.OddFrame
