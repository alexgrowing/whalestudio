import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaIntegralAlternatingSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaFunctionBoundedSupportStatement
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace

namespace GlobalTheory.Chamber.LanglandsFourier

variable {k : ℕ}

theorem tau_smul (P R : Finset (SV k)) (H : A0 k) {c : ℝ} (hc : 0 < c) : tau P R (c • H) = tau P R H := by
  unfold tau
  congr 1
  apply propext
  refine forall₂_congr fun u _ => ?_
  rw [inner_smul_right]
  exact mul_pos_iff_of_pos_left hc

theorem tauHat_smul (P R : Finset (SV k)) (H : A0 k) {c : ℝ} (hc : 0 < c) : tauHat P R (c • H) = tauHat P R H := by
  unfold tauHat
  congr 1
  apply propext
  refine forall₂_congr fun u _ => ?_
  rw [inner_smul_right]
  exact mul_pos_iff_of_pos_left hc

theorem gamP_smul (P R : Finset (SV k)) (H : A0 k) {c : ℝ} (hc : 0 < c) : gamP P R 0 (c • H) = gamP P R 0 H := by
  simp only [gamP, sub_zero, tau_smul _ _ _ hc, tauHat_smul _ _ _ hc]

theorem gamP_eq_zero (P R : Finset (SV k)) (hP : IsPar P) (hR : R ⊆ P) (H : A0 k) (hH : H ∈ aMQ (aP P) R)
    (h0 : H ≠ 0) : gamP P R 0 H = 0 := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.gamma_function_bounded_support k P R 0 hP hR
  by_contra hne
  have hn : 0 < ‖H‖ := norm_pos_iff.2 h0
  set c : ℝ := (|C| + 1) / ‖H‖ with hc
  have cpos : 0 < c := div_pos (by positivity) hn
  have := hC (c • H) (Submodule.smul_mem _ _ hH) (by rwa [gamP_smul _ _ _ cpos])
  rw [norm_smul, Real.norm_of_nonneg cpos.le, hc, div_mul_cancel₀ _ hn.ne'] at this
  linarith [le_abs_self C]

theorem wt_mem_aMQ (P S : Finset (SV k)) (hS : S ⊆ P) {u : SV k} (hu : u ∈ P) : wt S u ∈ aMQ (aP P) S := by
  refine ⟨?_, ?_⟩
  · exact sub_mem (Submodule.subset_span ⟨u, hu, rfl⟩) (vecSpan_mono hS (Submodule.starProjection_apply_mem _ _))
  · exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.Chamber.LanglandsFourier

open GlobalTheory.Chamber.LanglandsFourier in
theorem GlobalTheory.Chamber.langlands_fourier_sum : ∀ (k : ℕ) (P S : Finset (SV k)), IsPar P → S ⊆ P → S ≠ P → ∀ l ∈ generic k,
    ∑ R ∈ between P S, (-1 : ℂ) ^ (P \ R).card * epsHat P R l * eps R S l = 0 := by
  intro k P S hP hS hne l hl
  obtain ⟨-, hF⟩ := GlobalTheory.T.gamma_integral_alternating_sum k P S 0 hP hS
  have hF := hF l hl
  simp only [map_zero, sub_zero, eL, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hF
  rw [← hF]
  obtain ⟨u, hu⟩ : ∃ u, u ∈ P \ S := by
    by_contra h; push_neg at h
    exact hne (Subset.antisymm hS fun u hu => by by_contra h'; exact h u (mem_sdiff.2 ⟨hu, h'⟩))
  haveI : Nontrivial (aMQ (aP P) S) :=
    ⟨⟨⟨_, wt_mem_aMQ P S hS (mem_sdiff.1 hu).1⟩, 0, fun e => hP.wt_ne_zero hS hu (congrArg Subtype.val e)⟩⟩
  apply integral_eq_zero_of_ae
  have hae : ∀ᵐ H : aMQ (aP P) S, H ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hae] with H hH
  rw [gamP_eq_zero P S hP hS H H.2 (fun e => hH (Subtype.ext e))]
  simp
