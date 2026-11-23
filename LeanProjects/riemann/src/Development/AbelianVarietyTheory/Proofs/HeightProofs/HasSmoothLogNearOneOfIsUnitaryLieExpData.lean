import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hp : ∀ n : ℕ, σ (X ^ n) = σ X ^ n := fun n => by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, anti, ih, pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).map σ.toAddMonoidHom
    σ.continuous_of_finiteDimensional
  refine h1.unique ?_
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ X) using 1
  funext n
  simp [hp]

theorem exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hc : ContDiffAt ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) 0).contDiffAt
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := hasFDerivAt_exp_zero
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse hd hn, ?_, ?_, (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  · have := hc.to_localInverse hd hn
    rwa [NormedSpace.exp_zero] at this
  · have := (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at this
    exact this

theorem hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']

end GlobalTheory.SmoothForms
