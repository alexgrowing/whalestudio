import Mathlib

open Finset

noncomputable section

namespace Formalism.L2.SG.DensExact

def densProd (q : ℕ) (η : ℝ) (n m c : ℕ) : ℝ :=
  ∏ i ∈ Icc (n + 1 - (m + c)) n, (1 - η ^ i * ((q : ℝ) ^ i)⁻¹)

def countInert (K L : Type) [Fintype K] [Field L] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (Gm : Matrix (Fin m) (Fin m) L) : ℕ :=
  {X : Fin m → Fin n → L | LinearIndependent L X ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}.ncard

def countSplit (K : Type) [Field K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K) : ℕ :=
  {XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
      LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard

def DensExactInert : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L) (Gm : Matrix (Fin m) (Fin m) L),
      IsUnit Ph.det → (∀ k l, Ph l k = Ph k l ^ Fintype.card K) →
      (∀ i j, Gm j i = Gm i j ^ Fintype.card K) →
      (countInert K L n m Ph Gm : ℝ) /
          ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2)) =
        densProd (Fintype.card K) (-1) n m (m - Gm.rank)

def DensExactSplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K), IsUnit Ph.det →
      (countSplit K n m Ph Gm : ℝ) /
          ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2)) =
        densProd (Fintype.card K) 1 n m (m - Gm.rank)

def DensExact : Prop := DensExactInert ∧ DensExactSplit

def DensInertDisplay : Prop :=
  ∀ (q n m c : ℕ), 0 < q → c ≤ m → m + c ≤ n →
    (∏ j ∈ Icc (n - m + c + 1) n, (1 - ((-(q : ℝ)) ^ j)⁻¹)) *
        (∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 + (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹))) =
      densProd q (-1) n m c

def DensSplitDisplay : Prop :=
  ∀ (q n m c : ℕ), 0 < q → m + c ≤ n →
    (∏ i ∈ range m, (1 - ((q : ℝ) ^ (n - i))⁻¹)) *
        (∏ i ∈ range c, (1 - ((q : ℝ) ^ (n - m - i))⁻¹)) =
      densProd q 1 n m c

theorem prod_pairs (f : ℕ → ℝ) : ∀ (c N : ℕ), 2 * c ≤ N →
    ∏ i ∈ range c, (f (N - 2 * i) * f (N - 2 * i - 1)) = ∏ j ∈ Ico (N + 1 - 2 * c) (N + 1), f j := by
  intro c
  induction c with
  | zero => intro N _; simp
  | succ c ih =>
    intro N hN
    rw [prod_range_succ, ih N (by omega)]
    have h1 : N + 1 - 2 * (c + 1) < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h1]
    have h2 : N + 1 - 2 * (c + 1) + 1 < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h2]
    have e1 : N + 1 - 2 * (c + 1) + 1 + 1 = N + 1 - 2 * c := by omega
    have e3 : N + 1 - 2 * (c + 1) + 1 = N - 2 * c := by omega
    have e2 : N + 1 - 2 * (c + 1) = N - 2 * c - 1 := by omega
    rw [e1, e3, e2]
    ring

private theorem prod_range_sub_eq_prod_Ico (f : ℕ → ℝ) : ∀ (k N : ℕ), k ≤ N →
    ∏ i ∈ range k, f (N - i) = ∏ j ∈ Ico (N + 1 - k) (N + 1), f j := by
  intro k
  induction k with
  | zero => intro N _; simp
  | succ k ih =>
    intro N hN
    rw [prod_range_succ, ih N (by omega)]
    have h1 : N + 1 - (k + 1) < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h1]
    have e1 : N + 1 - (k + 1) + 1 = N + 1 - k := by omega
    have e2 : N + 1 - (k + 1) = N - k := by omega
    rw [e1, e2]
    ring

theorem densSplitDisplay_holds : DensSplitDisplay := by
  intro q n m c _ hmc
  have h1 : ∏ i ∈ range m, (1 - ((q : ℝ) ^ (n - i))⁻¹) =
      ∏ j ∈ Ico (n - m + 1) (n + 1), (1 - ((q : ℝ) ^ j)⁻¹) := by
    rw [show n - m + 1 = n + 1 - m by omega]
    exact prod_range_sub_eq_prod_Ico (fun j => 1 - ((q : ℝ) ^ j)⁻¹) m n (by omega)
  have h2 : ∏ i ∈ range c, (1 - ((q : ℝ) ^ (n - m - i))⁻¹) =
      ∏ j ∈ Ico (n - m + 1 - c) (n - m + 1), (1 - ((q : ℝ) ^ j)⁻¹) :=
    prod_range_sub_eq_prod_Ico (fun j => 1 - ((q : ℝ) ^ j)⁻¹) c (n - m) (by omega)
  have hD : densProd q 1 n m c =
      ∏ j ∈ Ico (n - m + 1 - c) (n + 1), (1 - ((q : ℝ) ^ j)⁻¹) := by
    unfold densProd
    have hI : Icc (n + 1 - (m + c)) n = Ico (n - m + 1 - c) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
    exact prod_congr rfl (fun i _ => by simp)
  rw [h1, h2, hD, ← prod_Ico_consecutive (fun j => 1 - ((q : ℝ) ^ j)⁻¹)
    (by omega : n - m + 1 - c ≤ n - m + 1) (by omega : n - m + 1 ≤ n + 1)]
  ring

theorem densInertDisplay_holds : DensInertDisplay := by
  intro q n m c _ hcm hmc
  have hA : ∏ j ∈ Icc (n - m + c + 1) n, (1 - ((-(q : ℝ)) ^ j)⁻¹) =
      ∏ j ∈ Ico (n - m + c + 1) (n + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) := by
    have hI : Icc (n - m + c + 1) n = Ico (n - m + c + 1) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
    refine prod_congr rfl (fun j _ => ?_)
    rcases neg_one_pow_eq_or ℝ j with h | h <;> simp [neg_pow, h]
  have hB : ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 + (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) =
      ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 - (-1 : ℝ) ^ (n - m + c - 2 * i - 1) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) := by
    refine prod_congr rfl (fun i hi => ?_)
    have hi' : i < c := mem_range.mp hi
    obtain ⟨k, hk⟩ : ∃ k, n - m + c - 2 * i = k + 1 := ⟨n - m + c - 2 * i - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  have hC : ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 - (-1 : ℝ) ^ (n - m + c - 2 * i - 1) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) =
      ∏ j ∈ Ico (n - m + c + 1 - 2 * c) (n - m + c + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) :=
    prod_pairs (fun j => 1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) c (n - m + c) (by omega)
  have hD : densProd q (-1) n m c =
      ∏ j ∈ Ico (n - m + c + 1 - 2 * c) (n + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) := by
    unfold densProd
    have hI : Icc (n + 1 - (m + c)) n = Ico (n - m + c + 1 - 2 * c) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
  rw [hA, hB, hC, hD, ← prod_Ico_consecutive (fun j => 1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹)
    (by omega : n - m + c + 1 - 2 * c ≤ n - m + c + 1) (by omega : n - m + c + 1 ≤ n + 1)]
  ring

end Formalism.L2.SG.DensExact
