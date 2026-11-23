import Formalism.FormalDegreeBessel.StatementDS

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

private def fdNum {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|

private def fdFull {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b : Fin n, (if a = b then 1 else |lam a - lam b|)

private lemma fdNum_nonneg {n : ℕ} (lam : Fin n → ℝ) : 0 ≤ fdNum lam :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _

private lemma fdNum_sq {n : ℕ} (lam : Fin n → ℝ) : fdNum lam ^ 2 = fdFull lam := by
  unfold fdNum fdFull
  have key : ∀ a b : Fin n, (if a = b then (1 : ℝ) else |lam a - lam b|) =
      (if a < b then |lam a - lam b| else 1) * (if b < a then |lam b - lam a| else 1) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, abs_sub_comm]
  simp_rw [key, Finset.prod_mul_distrib, ← Finset.prod_filter]
  rw [sq]
  congr 1
  symm
  exact Finset.prod_comm' (by intro a b; simp)

private lemma fdFull_perm {n : ℕ} (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    fdFull (lam ∘ σ) = fdFull lam := by
  unfold fdFull
  exact Fintype.prod_equiv σ _ _ fun a => Fintype.prod_equiv σ _ _ fun b => by
    simp [Equiv.apply_eq_iff_eq]

private lemma fdNum_perm {n : ℕ} (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    fdNum (lam ∘ σ) = fdNum lam := by
  refine (pow_left_inj₀ (fdNum_nonneg _) (fdNum_nonneg _) two_ne_zero).mp ?_
  rw [fdNum_sq, fdNum_sq, fdFull_perm]

private lemma fin_sub_pos {n : ℕ} {a b : Fin n} (h : a < b) :
    0 < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) :=
  sub_pos.mpr (Nat.cast_lt.mpr h)

theorem formal_degree_pos_holds : FdegPos := by
  intro n lam hl
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hl h))
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      fin_sub_pos (Finset.mem_filter.mp hb).2

theorem formal_degree_perm_holds : FdegPerm := by
  intro n lam σ
  have h := fdNum_perm lam σ
  unfold fdNum at h
  unfold fdegHC
  rw [h]

theorem formal_degree_vandermonde_holds : FdegVand := by
  intro n lam hl
  unfold fdegHC vand Formalism.QuantumDeterminants.rhoStd
  have h1 : ∀ a : Fin n, ∀ b ∈ univ.filter (fun b : Fin n => a < b),
      |lam a - lam b| = lam a - lam b := fun a b hb =>
    abs_of_pos (sub_pos.mpr (hl (Finset.mem_filter.mp hb).2))
  rw [Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl (h1 a)]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  ring

theorem formal_degree_weyl_holds : FdegWeyl := by
  intro n m hm
  unfold fdegHC
  simp_rw [Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  have hab := (Finset.mem_filter.mp hb).2
  have h2 := fin_sub_pos hab
  have h3 : (m b : ℝ) ≤ m a := by exact_mod_cast hm hab.le
  have e : (m a : ℝ) + Formalism.QuantumDeterminants.rhoStd n a - ((m b : ℝ) + Formalism.QuantumDeterminants.rhoStd n b) =
      (m a : ℝ) - m b + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; ring
  show |(m a : ℝ) + Formalism.QuantumDeterminants.rhoStd n a - ((m b : ℝ) + Formalism.QuantumDeterminants.rhoStd n b)| = _
  rw [e, abs_of_pos (by linarith)]

end Formalism.QuantumDeterminants
