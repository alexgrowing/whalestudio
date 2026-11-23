import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvKirA

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

theorem U_zero (c : Fin (m + 1)) : U c (0 : Fin (m + 1) → k) = 1 := Units.ext (colM_zero c)

theorem conj_U (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g)
    (x : Fin (m + 1) → k) :
    g * U ⟨j + 1, hj⟩ x = U ⟨j + 1, hj⟩ (fun p => ∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p r else 0) * x r) * g := by
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  have hrow : ∀ q, (g : Matrix _ _ k) c q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c q :=
    fun q => hg c q (fun h => lt_irrefl _ h.1)
  have hlow : ∀ p r : Fin (m + 1), ¬ p < c → r < c → (g : Matrix _ _ k) p r = 0 := fun p r hp hr => by
    rw [hg p r (fun h => hp (by rw [Fin.lt_def]; exact h.1)),
      Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hr))]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show (g : Matrix _ _ k) * colM c x = colM c _ * (g : Matrix _ _ k)
  ext p q
  simp only [colM, mul_add, add_mul, mul_one, one_mul, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, Matrix.of_apply]
  conv_rhs => rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ c) h)]
  by_cases hq : q = c
  · rw [hq, hrow c, Matrix.one_apply_eq, mul_one]
    by_cases hp : p < c
    · rw [if_pos ⟨rfl, hp⟩]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r < c
      · rw [if_pos ⟨rfl, hr⟩, if_pos hr]
      · rw [if_neg (fun h => hr h.2), if_neg hr]; simp
    · rw [if_neg (fun h => hp h.2)]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r < c
      · rw [hlow p r hp hr, zero_mul]
      · rw [if_neg (fun h => hr h.2), mul_zero]
  · rw [hrow q, Matrix.one_apply_ne (Ne.symm hq), mul_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg (fun h => hq h.1), mul_zero]

theorem decomp (j : ℕ) (hj : j < m + 1) (M : GL (Fin (m + 1)) k) (hM : InH (j + 1) M)
    (hrow : ∀ q, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, hj⟩ q) :
    ∃ y h, InH j h ∧ M = U ⟨j, hj⟩ y * h := by
  set jj : Fin (m + 1) := ⟨j, hj⟩ with hjj
  let y : Fin (m + 1) → k := fun p => (M : Matrix _ _ k) p jj
  refine ⟨y, U jj (-y) * M, ?_, ?_⟩
  · intro p q hpq
    show (colM jj (-y) * (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = _
    rw [colM, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single jj (fun r _ hr => by simp [hr]) (fun h => absurd (Finset.mem_univ jj) h)]
    rw [hrow q]
    by_cases hqj : q = jj
    · rw [hqj, Matrix.one_apply_eq, mul_one]
      by_cases hp : p < jj
      · rw [if_pos ⟨rfl, hp⟩, Matrix.one_apply_ne (ne_of_lt hp)]
        simp only [y, Pi.neg_apply]; ring
      · rw [if_neg (fun h => hp h.2), add_zero]
        by_cases hpe : p = jj
        · rw [hpe]; exact hrow jj
        · refine hM p jj (fun h => hp ?_)
          rw [Fin.lt_def]; rw [Fin.ext_iff] at hpe; simp [hjj] at h hpe ⊢; omega
    · rw [Matrix.one_apply_ne (fun h => hqj h.symm), mul_zero, add_zero]
      by_cases hpe : p = jj
      · rw [hpe]; exact hrow q
      · refine hM p q (fun h => hpq ⟨?_, ?_⟩)
        · rw [Fin.ext_iff] at hpe; simp [hjj] at hpe; omega
        · rw [Fin.ext_iff] at hqj; simp [hjj] at hqj; omega
  · rw [← mul_assoc, ← U_add, add_neg_cancel, U_zero, one_mul]

theorem InH_corner (g : GL (Fin m) k) : InH m (corner g) := by
  intro p q hpq
  rw [corner, val_emb₂, Matrix.reindex_apply, Matrix.submatrix_apply]
  induction p using Fin.addCases with
  | left a =>
    induction q using Fin.addCases with
    | left b => exact absurd ⟨by simp, by simp⟩ hpq
    | right b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
  | right a =>
    induction q using Fin.addCases with
    | left b => simp [stdSum, Matrix.one_apply, Fin.ext_iff]; omega
    | right b =>
      have := Subsingleton.elim a b
      subst this
      simp [stdSum]

end DiscreteGroups.sglob.LConvKir
