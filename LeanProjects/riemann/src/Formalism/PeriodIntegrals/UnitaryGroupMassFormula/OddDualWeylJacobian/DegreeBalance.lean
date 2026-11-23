import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace MiscB

theorem abel (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) :
    ∀ n, ∑ s ∈ Finset.range n, (s + 1) * (f s - f (s + 1)) + n * f n = ∑ s ∈ Finset.range n, f s
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← abel f hf n, add_assoc, ← Nat.mul_add,
      Nat.sub_add_cancel (hf n)]
    ring

def ext0 {k : ℕ} (ν : Fin k → ℕ) (t : ℕ) : ℕ := if h : t < k then ν ⟨t, h⟩ else 0

theorem degW_eq {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) : degW ν = ∑ s, ν s := by
  have hf : ∀ s, ext0 ν (s + 1) ≤ ext0 ν s := by
    intro s
    unfold ext0
    split_ifs with h1 h2
    · exact hν (Fin.mk_le_mk.2 (Nat.le_succ s))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := abel (ext0 ν) hf k
  have hk : ext0 ν k = 0 := by
    unfold ext0
    simp
  rw [hk, mul_zero, add_zero] at h
  have e1 : ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s) =
      ∑ s ∈ Finset.range k, (s + 1) * (ext0 ν s - ext0 ν (s + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => (s + 1) * (ext0 ν s - ext0 ν (s + 1))) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
    rfl
  have e2 : ∑ s : Fin k, ν s = ∑ s ∈ Finset.range k, ext0 ν s := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ext0 ν s) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
  unfold degW
  rw [e1, e2, h]

variable {m : ℕ} {lam : Fin (m + 1) → ℤ}

theorem nu_cast (hl : Antitone lam) (t : Fin (m + 1)) : (nuOf lam t : ℤ) = lam t - lam (Fin.last m) := by
  unfold nuOf
  exact Int.toNat_of_nonneg (sub_nonneg.2 (hl (Fin.le_last t)))

theorem nu_anti (hl : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have ha := nu_cast hl a
  have hb := nu_cast hl b
  have h := hl hab
  omega

theorem sum_nu_le (hl : Antitone lam) : ∑ t, nuOf lam t ≤ m * nuOf lam 0 := by
  rw [Fin.sum_univ_castSucc]
  have hl0 : nuOf lam (Fin.last m) = 0 := by
    unfold nuOf
    simp
  rw [hl0, add_zero]
  calc ∑ t : Fin m, nuOf lam t.castSucc ≤ ∑ _t : Fin m, nuOf lam 0 :=
        Finset.sum_le_sum fun t _ => nu_anti hl (Fin.zero_le _)
    _ = m * nuOf lam 0 := by simp

end MiscB

theorem degreeBalance : Bk := by
  intro m lam hl
  have hs : Antitone (lamStar lam) := fun i j hij => by
    unfold lamStar
    exact neg_le_neg (hl (Fin.rev_le_rev.2 hij))
  unfold expM
  rw [MiscB.degW_eq _ (MiscB.nu_anti hs), Nat.cast_sub (MiscB.sum_nu_le hl)]
  push_cast
  simp only [MiscB.nu_cast hs, MiscB.nu_cast hl]
  have hr : ∑ t : Fin (m + 1), (lamStar lam t - lamStar lam (Fin.last m)) =
      ∑ t : Fin (m + 1), (lam 0 - lam t) := by
    unfold lamStar
    rw [Fin.rev_last, ← Equiv.sum_comp Fin.revPerm (fun t => lam 0 - lam t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Fin.revPerm_apply]
    ring
  rw [hr]
  unfold lamStar
  rw [Fin.rev_last]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end PI.OddDualWeyl
