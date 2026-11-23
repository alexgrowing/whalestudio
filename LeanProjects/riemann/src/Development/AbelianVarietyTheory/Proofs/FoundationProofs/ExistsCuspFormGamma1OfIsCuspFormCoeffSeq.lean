import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma norm_petersson_self (k : ℕ) (h : ℍ → ℂ) (z : ℍ) :
    ‖petersson (k : ℤ) h h z‖ = ‖h z‖ ^ 2 * z.im ^ k := by
  simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  ring

lemma isZeroAtImInfty_of_bound (k : ℕ) (hk : 1 ≤ k) (h : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖h τ‖ ^ 2 * τ.im ^ k ≤ C) : IsZeroAtImInfty h := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hsq : Tendsto (fun τ : ℍ => ‖h τ‖ ^ 2) atImInfty (𝓝 0) := by
    have hlim : Tendsto (fun τ : ℍ => max C 0 * (τ.im)⁻¹) atImInfty (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp him).const_mul (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun τ => by positivity) ?_ hlim
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    have hpos : 0 < τ.im := τ.im_pos
    have hpow : τ.im ≤ τ.im ^ k := by
      calc τ.im = τ.im ^ 1 := (pow_one _).symm
        _ ≤ τ.im ^ k := pow_le_pow_right₀ hτ hk
    rw [le_mul_inv_iff₀ hpos]
    calc ‖h τ‖ ^ 2 * τ.im ≤ ‖h τ‖ ^ 2 * τ.im ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C := hC τ
      _ ≤ max C 0 := le_max_left _ _
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end GlobalTheory.EisM

theorem GlobalTheory.EisM.cuspForm_of_CF : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hNL hcf.1
  obtain ⟨C, hC⟩ := hcf.2
  have hall : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro γ
    refine isZeroAtImInfty_of_bound k hk _ C fun τ => ?_
    have h1 := congrArg norm (petersson_slash_SL (k : ℤ) (f : ℍ → ℂ) f γ τ)
    rw [norm_petersson_self, norm_petersson_self, hf] at h1
    rw [hf, h1]
    exact hC _
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, hf⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
