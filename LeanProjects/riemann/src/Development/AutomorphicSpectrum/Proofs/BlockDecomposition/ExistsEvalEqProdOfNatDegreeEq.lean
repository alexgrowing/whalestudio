import Mathlib

namespace GlobalTheory.CompanionTheory.AicSplit

open Polynomial

theorem exists_eval_eq_prod_of_natDegree_eq {B : Type} [CommRing B]
    (hB : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) (d : ℕ) :
    ∀ P : Polynomial B, P.Monic → P.natDegree = d →
      ∃ b : Fin d → B, ∀ a : B, P.eval a = ∏ j, (a - b j) := by
  induction d with
  | zero =>
    intro P hP hd
    refine ⟨fun j => j.elim0, fun a => ?_⟩
    have hc : P.coeff 0 = 1 := by
      rw [← hd]
      exact hP
    rw [eq_C_of_natDegree_eq_zero hd, hc, C_1, eval_one, Fin.prod_univ_zero]
  | succ d ih =>
    intro P hP hd
    rcases subsingleton_or_nontrivial B with hs | hs
    · exfalso
      have h0 : P = 0 := Polynomial.ext fun n => Subsingleton.elim _ _
      rw [h0, natDegree_zero] at hd
      omega
    · obtain ⟨a0, ha0⟩ := hB P hP (by rw [hd]; exact Nat.succ_pos d)
      have hroot : (X - C a0) * (P /ₘ (X - C a0)) = P :=
        mul_divByMonic_eq_iff_isRoot.mpr ha0
      have hQ : (P /ₘ (X - C a0)).Monic :=
        Monic.of_mul_monic_left (monic_X_sub_C a0) (by rw [hroot]; exact hP)
      have hQd : (P /ₘ (X - C a0)).natDegree = d := by
        have h := (monic_X_sub_C a0).natDegree_mul hQ
        rw [hroot, hd, natDegree_X_sub_C] at h
        omega
      obtain ⟨b', hb'⟩ := ih _ hQ hQd
      refine ⟨(Fin.cons a0 b' : Fin (d + 1) → B), fun a => ?_⟩
      have hev : P.eval a = (a - a0) * (P /ₘ (X - C a0)).eval a := by
        conv_lhs => rw [← hroot]
        rw [eval_mul, eval_sub, eval_X, eval_C]
      rw [hev, hb' a, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

theorem exists_eval_eq_prod (B : Type) [CommRing B]
    (hB : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Polynomial B) (hP : P.Monic) :
    ∃ b : Fin P.natDegree → B, ∀ a : B, P.eval a = ∏ j, (a - b j) :=
  exists_eval_eq_prod_of_natDegree_eq hB P.natDegree P hP rfl

end GlobalTheory.CompanionTheory.AicSplit
