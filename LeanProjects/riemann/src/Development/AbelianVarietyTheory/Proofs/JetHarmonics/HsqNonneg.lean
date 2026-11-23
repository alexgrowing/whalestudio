import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosureStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  unfold Hsq
  apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
  rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
  positivity

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have h2 : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1
  rw [h2]
  calc (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by ring
    _ ≤ A ^ n * A' ^ n := mul_le_mul h h' (by positivity) (by positivity)

theorem tau_bound : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = P.r + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
  intro hyp P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hN' hS ν hν I hI
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  by_cases hz : J ν = 0 ∨ J (ν + eZ I) = 0
  · rw [hS.tau_zero ν I hz, norm_zero]
    positivity
  rw [not_or] at hz
  have h1 : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
    by_contra hc
    exact hz.1 (hS.zero ν hc)
  have h2 : n1 (ν + eZ I) ≤ q0 ∧ NzOn (R (ν + eZ I)) (l (ν + eZ I)) ∧ NzOn (R (ν + eZ I)) (l' (ν + eZ I)) := by
    by_contra hc
    exact hz.2 (hS.zero _ hc)
  obtain ⟨-, -, -, hT, hT', hty, hty'⟩ := p.hP
  obtain ⟨νq, νq', hG, hG'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' hty hty'
  obtain ⟨io, pr, ep, hTens, hκ⟩ := hS.tau_eq ν hν
  obtain ⟨κ, κ', hk, hk', ht⟩ := hκ ⟨I, hI⟩ hz.1 hz.2
  have b1 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wp lam P.u b bv ga h q0 _ _ _ _ _ νq R l dg
    ⟨hN, hS.fam, hG, hS.left⟩ ν hν io pr ep hTens h1.2.1 ⟨I, hI⟩ κ h2.2.1 hk
  have b2 := GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hyp P.k P.r Wq lam P.u' b bv ga h q0 _ _ _ _ _ νq' R l' dg
    ⟨hN', hS.fam, hG', hS.right⟩ ν hν io pr ep hTens h1.2.2 ⟨I, hI⟩ κ' h2.2.2 hk'
  rw [hT] at b1
  rw [hT'] at b2
  have s1 := (hS.coef ν h1.1 h1.2.1 h1.2.2).2
  have s2 := (hS.coef _ h2.1 h2.2.1 h2.2.2).2
  have d1 := (hS.left ν h1.1).2.1
  have d2 := (hS.left _ h2.1).2.1
  have hep : ‖(ep ⟨I, hI⟩ : ℂ)‖ = 1 := by
    rcases hTens.ep_sq ⟨I, hI⟩ with h | h <;> simp [h]
  have ht' : tau ν I = (ep ⟨I, hI⟩ : ℂ) * κ' * star κ * s ν / s (ν + eZ I) := ht
  rw [ht', norm_div, norm_mul, norm_mul, norm_mul, hep, one_mul, norm_star, s1, s2]
  exact arith _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) d1 d2 (hsq_nonneg _ _ _) (hsq_nonneg _ _ _) b1 b2

end GlobalTheory.SupTau
