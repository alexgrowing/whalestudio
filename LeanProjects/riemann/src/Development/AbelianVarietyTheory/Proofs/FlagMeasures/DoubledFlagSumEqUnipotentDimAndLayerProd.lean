import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DoubledFlag

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.DoubledFlag.sum_range_double {M : Type} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) :
    ∑ s ∈ range (2 * a + 1), f s = ∑ i : Fin a, (f i + f (2 * a - i)) + f a := by
  rw [show 2 * a + 1 = (a + 1) + a by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => f i + f (2 * a - i)), Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun x => f (a + 1 + x)) a]
  have h : ∀ x ∈ range a, f (a + 1 + (a - 1 - x)) = f (2 * a - x) := fun x hx => by
    rw [Finset.mem_range] at hx; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel

open MeasureTheory NumberField Matrix Finset in

theorem _root_.GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = _root_.GlobalTheory.FlagMeas.dimN n j ∧ _root_.GlobalTheory.Count.layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  intro n a j D ν hj hD hD0 hν0 hν hna hsym
  have hJ : ν a = ∑ i, j i := by
    have h1 : ∀ m, m ≤ a → ν m = ∑ i ∈ range m, if h : i < a then j ⟨i, h⟩ else 0 := by
      intro m hm
      induction m with
      | zero => simp [hν0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), dif_pos (by omega)]
        exact hν ⟨m, by omega⟩
    rw [h1 a le_rfl, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < a then j ⟨i, h⟩ else 0)]
    simp
  have hmid : ν (a + 1) + ν a = n := by
    have h := (hsym a le_rfl).2
    rwa [show 2 * a + 1 - a = a + 1 by omega] at h
  have hlow : ∀ i : Fin a, (ν (i + 1) - ν i) * ν i = j i * ν i := by
    intro i; rw [hν i, Nat.add_sub_cancel_left]
  have hhigh : ∀ i : Fin a, (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i) + j i * ν (i + 1)
      = j i * n := by
    intro i
    have hi := i.isLt
    have h1 := (hsym i (by omega)).2
    have h2 := (hsym (i + 1) (by omega)).2
    have h3 := hν i
    rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
    rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
    rw [show ν (2 * a - i + 1) - ν (2 * a - i) = j i by omega, ← mul_add, h2]
  have hsq : ν a * ν a = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    have hsplit : ∀ i k : Fin a, j i * j k = ((if i < k then j i * j k else 0) +
        (if k < i then j k * j i else 0)) + (if i = k then j i ^ 2 else 0) := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp [sq]
      · simp [h, h.ne', not_lt.2 h.le]; ring
    rw [hJ, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_filter, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
    ring
  refine ⟨?_, ?_⟩
  · rw [_root_.GlobalTheory.DoubledFlag.sum_range_double]
    have hF : ∑ i : Fin a, ((ν (i + 1) - ν i) * ν i + (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i))
        + ∑ i, j i ^ 2 = n * ν a := by
      rw [← Finset.sum_add_distrib, hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := hhigh i
      rw [hν i] at h
      rw [hlow i]
      nlinarith
    unfold _root_.GlobalTheory.FlagMeas.dimN
    rw [← hJ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * ν a := ⟨n - 2 * ν a, by omega⟩
    rw [show ν (a + 1) - ν a = m by omega, show m + 2 * ν a - 2 * ν a = m by omega]
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ → ℝ, D = fun s => Real.exp (d s) :=
      ⟨fun s => Real.log (D s), funext fun s => (Real.exp_log (hD s)).symm⟩
    have hd0 : d 0 = 0 := by simpa using hD0
    have hdsym : ∀ s, s ≤ a → d (2 * a + 1 - s) = d s := fun s hs => by
      simpa using (hsym s hs).1
    have hc : ∀ i : Fin a, (Real.exp (d (i + 1)) / Real.exp (d i)) ^ (-(1 : ℝ) / j i)
        = Real.exp ((d i - d (i + 1)) / j i) := by
      intro i
      rw [← Real.exp_sub, ← Real.exp_mul]
      congr 1
      ring
    have htail : ∀ i : Fin a, ∑ k ∈ univ.filter (fun k => i < k), (j k : ℝ) = ν a - ν ((i : ℕ) + 1) := by
      intro i
      have hi := i.isLt
      have e : ∀ k : Fin a, (j k : ℝ) = ν ((k : ℕ) + 1) - ν k := fun k => by
        rw [hν k]; push_cast; ring
      simp only [e, Finset.sum_filter, Fin.lt_iff_val_lt_val]
      rw [Fin.sum_univ_eq_sum_range (fun x => if (i : ℕ) < x then (ν (x + 1) : ℝ) - ν x else 0) a,
        ← Finset.sum_filter,
        show (range a).filter (fun x => (i : ℕ) < x) = Ico ((i : ℕ) + 1) a by
          ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_sub (fun x => (ν x : ℝ)),
        Finset.sum_range_sub (fun x => (ν x : ℝ))]
      ring
    simp only [hc]
    unfold _root_.GlobalTheory.Count.layerProd
    simp only [id, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_neg,
      pow_one, mul_one]
    rw [Real.exp_eq_exp, ← hJ, _root_.GlobalTheory.DoubledFlag.sum_range_double, eq_neg_iff_add_eq_zero, ← add_assoc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := (univ : Finset (Fin a))) rfl (g := fun i : Fin a =>
        (2 * (ν ((i : ℕ) + 1) : ℝ) * d ((i : ℕ) + 1) - n * d ((i : ℕ) + 1)) - (2 * (ν i : ℝ) * d i - n * d i)) ?_,
      Fin.sum_univ_eq_sum_range (fun x => (2 * (ν (x + 1) : ℝ) * d (x + 1) - n * d (x + 1)) - (2 * (ν x : ℝ) * d x - n * d x)),
      Finset.sum_range_sub (fun x => 2 * (ν x : ℝ) * d x - n * d x)]
    · have hm : (ν (a + 1) : ℝ) = n - ν a := by rw [eq_sub_iff_add_eq]; exact_mod_cast hmid
      have hda : d (a + 1) = d a := by rw [← hdsym a le_rfl]; congr 1; omega
      rw [hm, hda, hν0, hd0]
      push_cast
      ring
    · intro i _
      have hi := i.isLt
      have hji : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      have h1 := (hsym i (by omega)).2
      have h2 := (hsym (i + 1) (by omega)).2
      rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
      rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
      have e1 : (ν (2 * a - i + 1) : ℝ) = n - ν i := by rw [eq_sub_iff_add_eq]; exact_mod_cast h1
      have e2 : (ν (2 * a - i) : ℝ) = n - ν ((i : ℕ) + 1) := by rw [eq_sub_iff_add_eq]; exact_mod_cast h2
      have e3 : (ν ((i : ℕ) + 1) : ℝ) = ν i + j i := by exact_mod_cast hν i
      have f1 : d (2 * a - i + 1) = d i := by rw [← hdsym i (by omega)]; congr 1; omega
      have f2 : d (2 * a - i) = d ((i : ℕ) + 1) := by rw [← hdsym (i + 1) (by omega)]; congr 1; omega
      rw [Finset.sum_congr rfl (g := fun k => 4 * (d i - d ((i : ℕ) + 1)) * (j k : ℝ))
          fun k _ => by push_cast; field_simp; ring, ← Finset.mul_sum, htail i, e1, e2, f1, f2, e3]
      push_cast [Nat.cast_sub hna]
      field_simp
      ring

end GlobalTheory.DoubledFlag
