import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore.ColumnMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowMat {d : ℕ} (j₀ : Fin d) (b : Fin d → k) : Matrix (Fin d) (Fin d) k :=
  Matrix.of fun j' j => if j' = j₀ then b j else 0

theorem mul_one_add_rowMat_apply {n d : ℕ} (j₀ : Fin d) (b : Fin d → k) (Y : Matrix (Fin n) (Fin d) k)
    (i : Fin n) (j : Fin d) : (Y * (1 + rowMat j₀ b) : Matrix (Fin n) (Fin d) k) i j = Y i j + Y i j₀ * b j := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  simp [rowMat, Matrix.mul_apply]

theorem rowMat_mul_rowMat {d : ℕ} (j₀ : Fin d) (b c : Fin d → k) (hc : c j₀ = 0) :
    rowMat j₀ c * rowMat j₀ b = 0 := by
  ext j' j
  simp [rowMat, Matrix.mul_apply, hc]

theorem rowMat_neg {d : ℕ} (j₀ : Fin d) (b : Fin d → k) : rowMat j₀ (-b) = - rowMat j₀ b := by
  ext j' j
  simp [rowMat]; split_ifs <;> simp

theorem one_add_rowMat_mul_neg {d : ℕ} (j₀ : Fin d) (b : Fin d → k) (hb : b j₀ = 0) :
    (1 + rowMat j₀ b) * (1 + rowMat j₀ (-b)) = 1 := by
  have h := rowMat_mul_rowMat j₀ (-b) b hb
  rw [rowMat_neg] at h ⊢
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h]
  abel

theorem mem_ebox_zero_iff {A D : Type} (ϖ : kˣ) (C X : Matrix A D k) (r : A → D → ℕ) :
    X ∈ ebox ϖ C r ↔ X - C ∈ ebox ϖ 0 r := by
  simp only [ebox, Set.mem_setOf_eq, Matrix.sub_apply, Matrix.zero_apply, sub_zero]

theorem mul_mem_ebox_zero {n d : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) ≤ 1) (j₀ : Fin d)
    (r : Fin n → Fin d → ℕ) (hr : ∀ i j, j ≠ j₀ → r i j ≤ r i j₀) (b : Fin d → k) (hb0 : b j₀ = 0)
    (hb : ∀ j, valuation k (b j) ≤ 1) (δ : Matrix (Fin n) (Fin d) k) (hδ : δ ∈ ebox ϖ 0 r) :
    δ * (1 + rowMat j₀ b) ∈ ebox ϖ 0 r := by
  have hδ' : ∀ i j, valuation k (δ i j) ≤ valuation k ((ϖ ^ r i j : kˣ) : k) := fun i j => by
    simpa using hδ i j
  intro i j
  simp only [Matrix.zero_apply, sub_zero]
  rw [mul_one_add_rowMat_apply]
  refine Valuation.map_add_le _ (hδ' i j) ?_
  by_cases hj : j = j₀
  · subst hj; simp [hb0]
  · rw [map_mul]
    calc valuation k (δ i j₀) * valuation k (b j)
        ≤ valuation k ((ϖ ^ r i j₀ : kˣ) : k) * 1 := mul_le_mul' (hδ' i j₀) (hb j)
      _ ≤ valuation k ((ϖ ^ r i j : kˣ) : k) := by
        rw [mul_one, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
        exact pow_le_pow_right_of_le_one' hϖ (hr i j hj)

theorem setOf_mul_mem_ebox {n d : ℕ} (ϖ : kˣ) (hϖ : valuation k (ϖ : k) ≤ 1) (j₀ : Fin d)
    (r : Fin n → Fin d → ℕ) (hr : ∀ i j, j ≠ j₀ → r i j ≤ r i j₀) (a : Fin d → k) (ha0 : a j₀ = 0)
    (ha : ∀ j, valuation k (a j) ≤ 1) (C P : Matrix (Fin n) (Fin d) k)
    (hCP : C * (1 + rowMat j₀ (-a)) = P) :
    {Y : Matrix (Fin n) (Fin d) k | Y * (1 + rowMat j₀ (-a)) ∈ ebox ϖ P r} = ebox ϖ C r := by
  have hna0 : (-a) j₀ = 0 := by simp [ha0]
  have hna : ∀ j, valuation k ((-a) j) ≤ 1 := fun j => by simpa using ha j
  ext Y
  simp only [Set.mem_setOf_eq]
  rw [mem_ebox_zero_iff, mem_ebox_zero_iff ϖ C, ← hCP, ← Matrix.sub_mul]
  constructor
  · intro h
    have := mul_mem_ebox_zero ϖ hϖ j₀ r hr a ha0 ha _ h
    rwa [Matrix.mul_assoc, show (1 + rowMat j₀ (-a)) * (1 + rowMat j₀ a) = 1 by
      simpa using one_add_rowMat_mul_neg j₀ (-a) hna0, Matrix.mul_one] at this
  · exact mul_mem_ebox_zero ϖ hϖ j₀ r hr (-a) hna0 hna _

theorem exists_unipotent_move : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ), IsUnif ϖ → ∀ (p₁ p₂ : Matrix (Fin n) (Fin d) k) (N : ℕ), 1 ≤ N → (∀ j, p₁ i₀ j = if j = j₀ then 1 else 0) → (∀ i, i ≠ i₀ → p₁ i j₀ = 0) → (∀ i, p₂ i j₀ = 0) → ∀ x₁ ∈ ebox ϖ p₁ (scaledBoxRadiiAtEntry i₀ j₀ N), ∃ h : GL (Fin d) k, {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₁ (baseCellRadiiAtEntry i₀ j₀ N)} = ebox ϖ x₁ (baseCellRadiiAtEntry i₀ j₀ N) ∧ {Y : Matrix (Fin n) (Fin d) k | Y * h.1 ∈ ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N)} = ebox ϖ p₂ (baseCellRadiiAtColumn j₀ N) := by
  intro k _ _ _ _ n d i₀ j₀ ϖ hϖ p₁ p₂ N hN hp₁ hp₁' hp₂ x₁ hx₁
  have hv : valuation k (ϖ : k) ≤ 1 := by
    rw [show valuation k (ϖ : k) = uniformizer k from hϖ]; exact uniformizer_lt_one.le
  set a : Fin d → k := fun j => if j = j₀ then 0 else x₁ i₀ j with ha_def
  have ha0 : a j₀ = 0 := by simp [a]
  have ha : ∀ j, valuation k (a j) ≤ 1 := by
    intro j
    by_cases hj : j = j₀
    · simp [a, hj]
    · have h1 := hx₁ i₀ j
      simp only [scaledBoxRadiiAtEntry, ne_eq, hj, not_false_eq_true, and_self, if_true, hp₁ j, if_neg hj, if_false, sub_zero] at h1
      simp only [a, if_neg hj]
      refine h1.trans ?_
      first
        | (rw [Units.val_pow_eq_pow_val, map_pow]; exact pow_le_one' hv _)
        | exact pow_le_one' hv _
  have hna0 : (-a) j₀ = 0 := by simp [ha0]
  let h : GL (Fin d) k :=
    ⟨1 + rowMat j₀ (-a), 1 + rowMat j₀ a,
      by simpa using one_add_rowMat_mul_neg j₀ (-a) hna0, one_add_rowMat_mul_neg j₀ a ha0⟩
  have hr1 : ∀ i j, j ≠ j₀ → baseCellRadiiAtEntry i₀ j₀ N i j ≤ baseCellRadiiAtEntry i₀ j₀ N i j₀ := by
    intro i j hj; simp only [baseCellRadiiAtEntry, hj, false_and, if_false]; split_ifs <;> omega
  have hr2 : ∀ i j, j ≠ j₀ → baseCellRadiiAtColumn (n := n) j₀ N i j ≤ baseCellRadiiAtColumn j₀ N i j₀ := by
    intro i j hj; simp only [baseCellRadiiAtColumn, hj, if_false, if_true]; omega
  let c : Matrix (Fin n) (Fin d) k := p₁ + Matrix.of fun i j => if i = i₀ then a j else 0
  have hc : c * (1 + rowMat j₀ (-a)) = p₁ := by
    ext i j
    rw [mul_one_add_rowMat_apply]
    by_cases hi : i = i₀
    · subst hi; simp [c, hp₁ j₀, ha0]
    · simp [c, hi, hp₁' i hi]
  have hxc : x₁ ∈ ebox ϖ c (baseCellRadiiAtEntry i₀ j₀ N) := by
    intro i j
    have h1 := hx₁ i j
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = j₀
      · subst hj; simpa [c, a, scaledBoxRadiiAtEntry, baseCellRadiiAtEntry] using h1
      · simp [c, a, hj, hp₁ j]
    · simpa [c, hi, scaledBoxRadiiAtEntry, baseCellRadiiAtEntry] using h1
  refine ⟨h, ?_, ?_⟩
  · rw [ebox_eq_of_mem hxc]
    exact setOf_mul_mem_ebox ϖ hv j₀ _ hr1 a ha0 ha c p₁ hc
  · refine setOf_mul_mem_ebox ϖ hv j₀ _ hr2 a ha0 ha p₂ p₂ ?_
    ext i j
    rw [mul_one_add_rowMat_apply]
    simp [hp₂ i]

end GlobalTheory.NormalCore.ColumnMove
