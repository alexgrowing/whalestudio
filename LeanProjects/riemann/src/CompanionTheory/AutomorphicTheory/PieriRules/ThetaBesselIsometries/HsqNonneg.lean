import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentClosureStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  show 0 ≤ max 1 T * b ^ (20 * (r + 1))
  have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ b ^ (20 * (r + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hsq : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  have hprod : (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by
    field_simp <;> ring
  have key : (a' * a * d / e) ^ 2 ≤ (Real.sqrt (A * A') ^ n) ^ 2 := by
    rw [hprod, hsq]
    exact mul_le_mul h h' (by positivity) (pow_nonneg hA n)
  have hl : 0 ≤ a' * a * d / e := by positivity
  have hr : 0 ≤ Real.sqrt (A * A') ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc a' * a * d / e = Real.sqrt ((a' * a * d / e) ^ 2) := (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((Real.sqrt (A * A') ^ n) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (A * A') ^ n := Real.sqrt_sq hr

theorem tau_bound : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → SupG p lam q0 R l l' dg s J tau → ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 → ∀ I : Finset (Fin (2 * P.r + P.k + 1)), I.card = P.r + 1 → ‖tau ν I‖ ≤ Real.sqrt (Hsq P.r P.T b * Hsq P.r P.T' b) ^ (P.r + 1) := by
  intro hG P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hN' hS ν hν I hI
  by_cases hJ : J ν = 0 ∨ J (ν + eZ I) = 0
  · rw [hS.tau_zero ν I hJ, norm_zero]
    exact pow_nonneg (Real.sqrt_nonneg _) _
  · obtain ⟨hJ1, hJ2⟩ := not_or.mp hJ
    obtain ⟨io, pr, ep, hT, hall⟩ := hS.tau_eq ν hν
    obtain ⟨κ, κ', hκ, hκ', htau⟩ := hall ⟨I, hI⟩ hJ1 hJ2
    have hκbb : ‖κ‖ ^ 2 * dg ν / dg (ν + eZ I) ≤ Hsq P.r P.T b ^ (P.r + 1) ∧
        ‖κ'‖ ^ 2 * dg ν / dg (ν + eZ I) ≤ Hsq P.r P.T' b ^ (P.r + 1) ∧
        0 < dg ν ∧ 0 < dg (ν + eZ I) ∧ ‖s ν‖ = dg ν ∧ ‖s (ν + eZ I)‖ = dg (ν + eZ I) := by
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      haveI : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq
      have hz1 : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
        by_contra hc
        exact hJ1 (hS.zero ν hc)
      have hz2 : n1 (ν + eZ I) ≤ q0 ∧ NzOn (R (ν + eZ I)) (l (ν + eZ I)) ∧
          NzOn (R (ν + eZ I)) (l' (ν + eZ I)) := by
        by_contra hc
        exact hJ2 (hS.zero (ν + eZ I) hc)
      have hd1 : 0 < dg ν := (hS.left ν hz1.1).2.1
      have hd2 : 0 < dg (ν + eZ I) := (hS.left (ν + eZ I) hz2.1).2.1
      have hs1 : ‖s ν‖ = dg ν := (hS.coef ν hz1.1 hz1.2.1 hz1.2.2).2
      have hs2 : ‖s (ν + eZ I)‖ = dg (ν + eZ I) := (hS.coef (ν + eZ I) hz2.1 hz2.2.1 hz2.2.2).2
      have hPl := p.hP
      obtain ⟨νq, hνq⟩ := besselSide_of_isType P.k P.r Wp p.T.base.z p.T.base.π P.u p.T.base.μW p.T.base.μN
        p.T.base.μG hN.1 p.T.base.z_mem p.T.base.T_pos p.T.base.haarW p.T.base.haarN p.T.base.haarG
        hPl.2.2.2.2.2.1
      obtain ⟨νq', hνq'⟩ := besselSide_of_isType P.k P.r Wq p.T.base.z' p.T.base.π' P.u' p.T.base.μW'
        p.T.base.μN p.T.base.μG hN'.1 p.T.base.z'_mem p.T.base.T'_pos p.T.base.haarW' p.T.base.haarN
        p.T.base.haarG hPl.2.2.2.2.2.2
      have hb1 := Gp91.GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hG P.k P.r Wp lam P.u b bv ga h q0 p.T.base.z p.T.base.π p.T.base.μW
        p.T.base.μN p.T.base.μG νq R l dg ⟨hN, hS.fam, hνq, hS.left⟩ ν hν io pr ep hT hz1.2.1 ⟨I, hI⟩ κ hz2.2.1 hκ
      have hb2 := Gp91.GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le hG P.k P.r Wq lam P.u' b bv ga h q0 p.T.base.z' p.T.base.π' p.T.base.μW'
        p.T.base.μN p.T.base.μG νq' R l' dg ⟨hN', hS.fam, hνq', hS.right⟩ ν hν io pr ep hT hz1.2.2 ⟨I, hI⟩ κ' hz2.2.2 hκ'
      rw [hPl.2.2.2.1] at hb1
      rw [hPl.2.2.2.2.1] at hb2
      exact ⟨hb1, hb2, hd1, hd2, hs1, hs2⟩
    obtain ⟨hκb, hκb', hd1, hd2, hs1, hs2⟩ := hκbb
    have htau' : tau ν I = ↑(ep ⟨I, hI⟩) * κ' * star κ * s ν / s (ν + eZ I) := htau
    obtain ⟨-, hep, -, -⟩ := hT
    have hepn : ‖((ep ⟨I, hI⟩ : ℝ) : ℂ)‖ = 1 := by
      rcases hep ⟨I, hI⟩ with h1 | h1 <;> simp [h1]
    rw [htau', norm_div, norm_mul, norm_mul, norm_mul, hepn, norm_star, hs1, hs2, one_mul]
    exact arith ‖κ‖ ‖κ'‖ (dg ν) (dg (ν + eZ I)) (Hsq P.r P.T b) (Hsq P.r P.T' b) (P.r + 1) (norm_nonneg _)
      (norm_nonneg _) hd1 hd2 (hsq_nonneg _ _ _) (hsq_nonneg _ _ _) hκb hκb'

end GlobalTheory.SupTau
