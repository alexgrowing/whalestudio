import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PolUnitary

theorem tri_add' (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem dual_coeff_mul {q : ℂ} (hq : q ≠ 0) {r : ℕ} {f : ℂ[X]} (hf : f ≠ 0) (hd : f.natDegree = r) {k : ℕ} (hk : k ≤ r) :
    (dualPoly (q ^ (r - 1)) f).coeff k / ((-1) ^ k * q ^ (k * (k - 1) / 2)) *
        (f.coeff r / ((-1) ^ r * q ^ (r * (r - 1) / 2))) =
      f.coeff (r - k) / ((-1) ^ (r - k) * q ^ ((r - k) * (r - k - 1) / 2)) := by
  have htop : f.coeff r ≠ 0 := by
    rw [← hd]; exact leadingCoeff_ne_zero.2 hf
  rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hk), leadingCoeff, hd]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, ← pow_mul]
  have e := congrArg (fun m => q ^ m) (tri_add' k j)
  simp only [pow_add] at e
  have e2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have n1 : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by simp)
  have n2 : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by simp)
  have n3 : ∀ m : ℕ, q ^ m ≠ 0 := fun m => pow_ne_zero _ hq
  rw [pow_add]
  generalize (-1 : ℂ) ^ k = u at *
  generalize (-1 : ℂ) ^ j = v at *
  have m1 := n3 ((k + j) * (k + j - 1) / 2)
  have m2 := n3 (k * (k - 1) / 2)
  have m3 := n3 (j * (j - 1) / 2)
  generalize q ^ ((k + j) * (k + j - 1) / 2) = A at *
  generalize q ^ (k * (k - 1) / 2) = B at *
  generalize q ^ (j * (j - 1) / 2) = C' at *
  generalize q ^ ((k + j - 1) * k) = D at *
  rw [div_mul_div_comm, div_eq_div_iff (by simp [n1, n2, m1, m2]) (by simp [n2, m3])]
  have e3 := inv_mul_cancel₀ htop
  linear_combination (f.coeff j * D * v * C') * e3 - (f.coeff j * v) * e - (f.coeff j * v * A * B) * e2

theorem conj_eq_dual : ∀ (q r : ℕ) (f : ℂ[X]) (a w : ℕ → ℂ), q ≠ 0 → f.coeff 0 = 1 → f.natDegree ≤ r → (∀ k, a k = (f.map (starRingEnd ℂ)).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → (∀ k, w k = (dualPoly ((q : ℂ) ^ (r - 1)) f).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → ((a r ≠ 0 ∧ ∀ k ≤ r, star (a k) * a r = a (r - k)) ∨ (w r ≠ 0 ∧ ∀ k ≤ r, star (w k) * w r = w (r - k))) → ∀ k ≤ r, a k = w k := by
  intro q r f a w hq h0 hdeg ha hw hrel k hk
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hf : f ≠ 0 := ne_zero_of_coeff_zero h0
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ k, c k = f.coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) := ⟨_, fun _ => rfl⟩
  have hac : ∀ k, a k = star (c k) := by
    intro k
    rw [ha, hc, coeff_map]
    simp
  have key : f.natDegree = r → ∀ k ≤ r, w k * c r = c (r - k) := by
    intro hd k hk
    rw [hw, hc, hc]
    exact dual_coeff_mul hqc hf hd hk
  have hc0 : c 0 = 1 := by rw [hc, h0]; simp
  rcases hrel with ⟨hr, hrel⟩ | ⟨hr, hrel⟩
  · have hcr : c r ≠ 0 := by
      intro h
      apply hr
      rw [hac, h, star_zero]
    have hd : f.natDegree = r := by
      refine le_antisymm hdeg (le_natDegree_of_ne_zero fun h => hcr ?_)
      rw [hc, h, zero_div]
    have h1 := congrArg star (hrel k hk)
    rw [star_mul', star_star, hac r, hac (r - k), star_star, star_star, ← key hd k hk] at h1
    exact mul_right_cancel₀ hcr h1
  · have hd : f.natDegree = r := by
      refine le_antisymm hdeg (not_lt.1 fun h => hr ?_)
      rw [hw, coeff_dualPoly_of_lt _ _ h, zero_div]
    have h1 := key hd r le_rfl
    rw [Nat.sub_self, hc0] at h1
    have h2 := key hd (r - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk, ← hrel k hk, mul_assoc, h1, mul_one] at h2
    rw [hac, ← h2, star_star]

end GlobalTheory.PolUnitary
