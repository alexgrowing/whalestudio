import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLevi

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def edge (c d : L) (f : Fin N → L) : Fin (N + 2) → L := Fin.cons c (Fin.snoc f d : Fin (N + 1) → L)

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_zero (c d : L) (f : Fin N → L) : edge c d f 0 = c := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_mid (c d : L) (f : Fin N → L) (j : Fin N) : edge c d f (mid j) = f j := by
  simp [edge, mid]

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_last (c d : L) (f : Fin N → L) : edge c d f (Fin.last (N + 1)) = d := by
  rw [edge, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

def blkMat (x y : L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  fun i j => edge (edge x 0 (fun _ => 0) j) (edge 0 y (fun _ => 0) j) (fun p => edge 0 0 (A p) j) i

theorem gram_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ k, σ (M k i) * M k.rev j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.rev]
  · rw [if_pos (by have := k.isLt; simp only [Fin.val_rev]; omega), mul_one]
  · intro l _ hl
    rw [if_neg, mul_zero, zero_mul]
    intro h
    apply hl
    ext
    have := k.isLt
    have := l.isLt
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blkMat_gram {x y : L} (hxy : σ x * y = 1) (hyx : σ y * x = 1) {A : Matrix (Fin N) (Fin N) L}
    (hA : cT σ A * antiJ L N * A = antiJ L N) :
    cT σ (blkMat x y A) * antiJ L (N + 2) * blkMat x y A = antiJ L (N + 2) := by
  ext i j
  rw [gram_apply, sum_idx]
  simp only [Fin.rev_last, ← mid_rev, Fin.rev_zero]
  rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl
  · simp [blkMat, antiJ]
  · simp [blkMat, antiJ, val_mid, s.isLt.ne]
  · simp [blkMat, antiJ, hxy]
  · simp [blkMat, antiJ, val_mid, r.isLt.ne]
  · have h := congrFun (congrFun hA r) s
    rw [gram_apply] at h
    simp only [blkMat, edge_zero, edge_mid, edge_last, map_zero, zero_mul, mul_zero, zero_add, add_zero]
    rw [h]
    simp only [antiJ]
    have e1 := val_mid r
    have e2 := val_mid s
    by_cases h1 : (r : ℕ) + s + 1 = N
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ, hyx]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ]

theorem leviExists : LeviExists := by
  intro L _ _ ϖ σ q N hU a g₀
  obtain ⟨_, _, hσϖ, hvϖ, _⟩ := hU
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hvϖ
  have hσx : σ (ϖ ^ a) = ϖ ^ a := by rw [map_zpow₀, hσϖ]
  have hσy : σ (ϖ ^ (-a)) = ϖ ^ (-a) := by rw [map_zpow₀, hσϖ]
  have hxy : σ (ϖ ^ a) * ϖ ^ (-a) = 1 := by rw [hσx, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyx : σ (ϖ ^ (-a)) * ϖ ^ a = 1 := by rw [hσy, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero]
  have hA : cT σ (mat g₀) * antiJ L N * mat g₀ = antiJ L N := g₀.2
  have hJJ : antiJ L (N + 2) * antiJ L (N + 2) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, antiJ, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    have hi := i.isLt
    have hj := j.isLt
    rw [Finset.sum_eq_single i.rev]
    · rw [if_pos (by simp only [Fin.val_rev]; omega)]
      by_cases h : i = j
      · subst h
        rw [if_pos (by simp only [Fin.val_rev]; omega), if_pos rfl]
      · rw [if_neg (by simp only [Fin.val_rev]; intro h'; apply h; ext; omega), if_neg h]
    · intro l _ hl
      rw [if_neg]
      intro h'
      apply hl
      ext
      have := l.isLt
      simp only [Fin.val_rev]
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := blkMat (ϖ ^ a) (ϖ ^ (-a)) (mat g₀) with hB
  have hG : cT σ B * antiJ L (N + 2) * B = antiJ L (N + 2) := blkMat_gram hxy hyx hA
  have hCB : antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B = 1 := by
    calc antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B
        = antiJ L (N + 2) * (cT σ B * antiJ L (N + 2) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, hJJ]
  have hBC : B * (antiJ L (N + 2) * cT σ B * antiJ L (N + 2)) = 1 := mul_eq_one_comm.mp hCB
  let U : GL (Fin (N + 2)) L := ⟨B, antiJ L (N + 2) * cT σ B * antiJ L (N + 2), hBC, hCB⟩
  have hU : U ∈ GU σ (N + 2) := hG
  refine ⟨⟨U, hU⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    show B i j = 0
    rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl <;>
      simp [hB, blkMat, blk_zero, blk_mid, blk_last] at hij ⊢
  · show B 0 0 = ϖ ^ a
    simp [hB, blkMat]
  · show B (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a)
    simp [hB, blkMat]
  · intro i j
    show B (mid i) (mid j) = mat g₀ i j
    simp [hB, blkMat]

end GlobalTheory.CompanionTheory.InertLevi

end
