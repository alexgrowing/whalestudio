import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApplyMulOfCoprime
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeEig

theorem hsum_succ (α β : ℂ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1 + 1), α ^ i * β ^ (j + 1 - i) =
      α ^ (j + 1) + β * ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
    ring

theorem e2a : E2a := by
  intro k N χ a h
  obtain ⟨_, h1, hH⟩ := h
  have hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n := by
    intro p hp n _ hpn
    have := hH p n hp
    rw [if_neg hpn, add_zero] at this
    exact this.symm
  have hrec : ∀ p, p.Prime → ∀ n, 0 < n →
      a (p * (p * n)) = a p * a (p * n) - (χ p * (p : ℂ) ^ (k - 1)) * a n := by
    intro p hp n _
    have := hH p (p * n) hp
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at this
    rw [this]; ring
  refine ⟨fun m n hmn => GlobalTheory.CompanionTheory.HeckeMult.apply_mul_of_coprime a
      (fun p => χ p * (p : ℂ) ^ (k - 1)) h1 hcop hrec m n hmn, ?_⟩
  intro p hp α β hs hp' j
  induction j using Nat.twoStepInduction with
  | zero => simp [h1]
  | one =>
    simp [Finset.sum_range_succ]
    rw [← hs]
    ring
  | more j ih0 ih1 =>
    have r := hH p (p ^ (j + 1)) hp
    have hd : p ^ (j + 1) / p = p ^ j := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    have hm : p * p ^ (j + 1) = p ^ (j + 2) := by ring
    rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero j)), hd, hm] at r
    have e : a (p ^ (j + 2)) = a p * a (p ^ (j + 1)) - χ p * (p : ℂ) ^ (k - 1) * a (p ^ j) := by
      rw [r]; ring
    rw [e, ih1, ih0, ← hs, ← hp', show j + 2 = j + 1 + 1 by omega, hsum_succ α β (j + 1), hsum_succ α β j]
    ring

end GlobalTheory.CompanionTheory.HeckeEig
