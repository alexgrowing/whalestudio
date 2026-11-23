import Mathlib

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Pmono

lemma prod_digits_sq (p f : ℕ) (P : NNReal) (y : Fin f → NNReal) (hy : ∀ n, y n ^ (p - 1) = P) :
    (∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ)) ^ 2 = P ^ (f * p ^ f) := by
  have hrev : ∏ d : Fin f → Fin p, ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) =
      ∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ) :=
    Fintype.prod_equiv (Equiv.piCongrRight fun _ => Fin.revPerm) _ _ (fun d => rfl)
  rw [sq]
  nth_rewrite 2 [← hrev]
  rw [← Finset.prod_mul_distrib]
  have hterm : ∀ d : Fin f → Fin p,
      (∏ n, y n ^ (d n : ℕ)) * ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P ^ f := by
    intro d
    rw [← Finset.prod_mul_distrib]
    have h : ∀ n, y n ^ (d n : ℕ) * y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P := by
      intro n
      rw [← pow_add, Fin.val_rev, ← hy n]
      congr 1
      have := (d n).isLt
      omega
    rw [Finset.prod_congr rfl (fun n _ => h n)]
    simp
  rw [Finset.prod_congr rfl (fun d _ => hterm d)]
  simp [← pow_mul, mul_comm]

lemma eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → NNReal) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) (h : ∏ i, b i = ∏ i, a i) (i : ι) : b i = a i := by
  refine le_antisymm ?_ (hab i)
  have hQ : 0 < ∏ j ∈ Finset.univ.erase i, a j := Finset.prod_pos (fun j _ => ha j)
  have h1 : ∏ j ∈ Finset.univ.erase i, a j ≤ ∏ j ∈ Finset.univ.erase i, b j :=
    Finset.prod_le_prod' (fun j _ => hab j)
  have h2 : b i * ∏ j ∈ Finset.univ.erase i, a j ≤ a i * ∏ j ∈ Finset.univ.erase i, a j :=
    calc b i * ∏ j ∈ Finset.univ.erase i, a j ≤ b i * ∏ j ∈ Finset.univ.erase i, b j :=
          mul_le_mul' le_rfl h1
      _ = ∏ j, b j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      _ = ∏ j, a j := h
      _ = a i * ∏ j ∈ Finset.univ.erase i, a j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  exact le_of_mul_le_mul_right h2 hQ

theorem count : ∀ (p f : ℕ), 2 ≤ p → ∀ (P : NNReal), P ≠ 0 → ∀ (x xD : Fin f → NNReal) (X XD : (Fin f → Fin p) → NNReal), (∀ n, (x n * xD n) ^ (p - 1) = P) → (∀ d, ∏ n, x n ^ (d n : ℕ) ≤ X d) → (∀ d, ∏ n, xD n ^ (d n : ℕ) ≤ XD d) → (∏ d, X d * XD d) ^ 2 = P ^ (f * p ^ f) → ∀ d, X d = ∏ n, x n ^ (d n : ℕ) ∧ XD d = ∏ n, xD n ^ (d n : ℕ) := by
  intro p f hp P hP x xD X XD hxy hX hXD hprod d
  have hne : ∀ n, x n ≠ 0 ∧ xD n ≠ 0 := by
    intro n
    have hmul : x n * xD n ≠ 0 := by
      intro h0
      have h := hxy n
      rw [h0, zero_pow (by omega)] at h
      exact hP h.symm
    exact ⟨left_ne_zero_of_mul hmul, right_ne_zero_of_mul hmul⟩
  have hApos : ∀ d : Fin f → Fin p, 0 < ∏ n, x n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).1) _)
  have hBpos : ∀ d : Fin f → Fin p, 0 < ∏ n, xD n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).2) _)
  have hsq : (∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ)) ^ 2 =
      P ^ (f * p ^ f) := by
    rw [← PositivityTheory.HtPt.Pmono.prod_digits_sq p f P (fun n => x n * xD n) hxy]
    congr 1
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun n _ => (mul_pow _ _ _).symm
  have heq : ∏ d, X d * XD d = ∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ) :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp (hprod.trans hsq.symm)
  have hd := PositivityTheory.HtPt.Pmono.eq_of_prod_eq
    (fun d : Fin f → Fin p => (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ))
    (fun d => X d * XD d) (fun d => mul_pos (hApos d) (hBpos d))
    (fun d => mul_le_mul' (hX d) (hXD d)) heq d
  have hXDpos : 0 < XD d := lt_of_lt_of_le (hBpos d) (hXD d)
  have hXpos : 0 < X d := lt_of_lt_of_le (hApos d) (hX d)
  constructor
  · refine le_antisymm ?_ (hX d)
    have h1 : X d * XD d ≤ (∏ n, x n ^ (d n : ℕ)) * XD d :=
      hd.le.trans (mul_le_mul' le_rfl (hXD d))
    exact le_of_mul_le_mul_right h1 hXDpos
  · refine le_antisymm ?_ (hXD d)
    have h1 : X d * XD d ≤ X d * ∏ n, xD n ^ (d n : ℕ) :=
      hd.le.trans (mul_le_mul' (hX d) le_rfl)
    exact le_of_mul_le_mul_left h1 hXpos

end PositivityTheory.HtPt.Pmono
