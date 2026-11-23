import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantHermitianFormNonnegOfCloudEigenStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormHhJSelfLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevelStatement

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_normSq_proj_single_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hA hS hj hw c
  have hnorm : ∀ s, ‖pr s (Pi.single c w)‖ ^ 2 =
      ‖hhJ ε (io s (pr s (Pi.single c w))) (io s (pr s (Pi.single c w)))‖ := by
    intro s
    obtain ⟨e, he, hs⟩ := hA.sign s
    rw [hs, norm_mul, inner_self_eq_norm_sq_to_K]
    rcases he with rfl | rfl <;> simp
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hE.2.1 (fun s => (hF s).2.1) hA hw
  have hproj := GlobalTheory.T.cloudNode_projection_norm_lowLevel M n ε E N F io pr μ kk j bv w hE hF hA hS hj hw c
  have hq := GlobalTheory.T.sum_norm_hhJ_self_le_of_orthogonal M n ε (fun s => io s (pr s (Pi.single c w)))
    (univ.filter (fun a : Fin n => a.val + 1 < kk)) (18 / 13) (3 * (6 * bv) ^ (n - kk)) (‖w‖ ^ 2)
    (fun s t hst => hA.orth s t hst _ _)
    (fun s hs => GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen M n ε E μ kk (j + 2) bv _ hE hS (by omega) (fun d => hcomp s c d) s
      (Finset.mem_filter.1 hs).2 (GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hE hF hA s _))
    hproj.1
    (fun s hs => hproj.2 s (by simpa using hs))
  obtain ⟨h1, h2, -, -, -, hb⟩ := hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnb : (n : ℝ) ≤ bv := by
    have h7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    nlinarith
  obtain ⟨hcard, harith⟩ := GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv h1 h2 hnb
  have hcompl : (univ.filter (fun a : Fin n => a.val + 1 < kk))ᶜ =
      univ.filter (fun a : Fin n => kk ≤ a.val + 1) := by
    ext a; simp
  rw [hcompl, hcard] at hq
  rw [Finset.sum_congr rfl (fun s _ => hnorm s)]
  exact hq.trans (mul_le_mul_of_nonneg_right harith (by positivity))

end GlobalTheory
