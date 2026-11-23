import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.Glue

variable {K : Type} [Field K] {g : ℕ}

def cramerCoef (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) (k : Fin g)
    (j : Fin ((k : ℕ) + 1)) : K :=
  (-1) ^ ((k : ℕ) + (j : ℕ)) * (Matrix.of fun a b : Fin k => H (σ k a) (Fin.castLE k.2 (j.succAbove b))).det /
    minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1))

def cramerTri (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) : Matrix (Fin g) (Fin g) K :=
  Matrix.of fun l k => ∑ j : Fin ((k : ℕ) + 1), if Fin.castLE k.2 j = l then cramerCoef H σ k j else 0

theorem minorAt_snoc_expand (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) (k : Fin g)
    (r : Fin (g + g)) :
    minorAt H ((k : ℕ) + 1) k.2 (Fin.snoc (σ k) r) = ∑ j : Fin ((k : ℕ) + 1),
      (-1) ^ ((k : ℕ) + (j : ℕ)) * H r (Fin.castLE k.2 j) *
        (Matrix.of fun a b : Fin k => H (σ k a) (Fin.castLE k.2 (j.succAbove b))).det := by
  unfold minorAt
  rw [Matrix.det_succ_row _ (Fin.last k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.val_last, Matrix.of_apply, Fin.snoc_last]
  congr 2
  ext a b
  simp [Fin.succAbove_last, Fin.snoc_castSucc]

theorem cramerCol_eq_mul (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) :
    cramerCol H σ = H * cramerTri H σ := by
  ext r k
  rw [Matrix.mul_apply]
  simp only [cramerCol, cramerTri, Matrix.of_apply, minorAt_snoc_expand, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, cramerCoef]
  ring

theorem cramerTri_blockTriangular (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) :
    (cramerTri H σ).BlockTriangular id := by
  intro l k hkl
  simp only [cramerTri, Matrix.of_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  intro h
  have := j.2
  have h2 : ((Fin.castLE k.2 j : Fin g) : ℕ) = l := by rw [h]
  simp only [Fin.coe_castLE] at h2
  simp only [id] at hkl
  have : (k : ℕ) < l := hkl
  omega

theorem cramerTri_diag (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) (k : Fin g) :
    cramerTri H σ k k = minorAt H k k.2.le (σ k) / minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) := by
  simp only [cramerTri, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · rw [if_pos (by ext; simp), cramerCoef]
    have hs : ((-1 : K)) ^ ((k : ℕ) + ((Fin.last (k : ℕ)) : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]; simp
    rw [hs, one_mul]
    congr 1
    unfold minorAt
    congr 1
    ext a b
    simp only [Matrix.of_apply, Fin.succAbove_last]
    congr 1
  · intro j _ hj
    rw [if_neg]
    intro h
    apply hj
    have h2 : ((Fin.castLE k.2 j : Fin g) : ℕ) = k := by rw [h]
    simp only [Fin.coe_castLE] at h2
    ext; simp [h2]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.WholeFlag.Glue

namespace GlobalTheory.WholeFlag.Glue

theorem prod_range_telescope {K : Type} [Field K] (f : ℕ → K) (g : ℕ) (hf : ∀ k, k ≤ g → f k ≠ 0) :
    ∀ n, n ≤ g → ∏ k ∈ Finset.range n, f k / f (k + 1) = f 0 / f n := by
  intro n
  induction n with
  | zero => intro _; simp [div_self (hf 0 (Nat.zero_le _))]
  | succ n ih =>
    intro hn
    rw [Finset.prod_range_succ, ih (by omega)]
    have h1 := hf n (by omega)
    field_simp

theorem rowSel_mul_det {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (τ : Fin g → Fin (g + g)) :
    Matrix.det ((rowSel τ : Matrix (Fin g) (Fin (g + g)) K) * H) = minorAt H g le_rfl τ := by
  unfold minorAt
  congr 1
  ext l k
  rw [Matrix.mul_apply]
  simp [rowSel]

theorem cramerCol_tri_det :
    ∀ {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)),
      (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → ∃ B : Matrix (Fin g) (Fin g) K, B.BlockTriangular id ∧
        (∀ k : Fin g, B k k = minorAt H k k.2.le (σ k) / minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1))) ∧
        cramerCol H σ = H * B ∧ (rowSel (σ g) * cramerCol H σ).det = 1 := by
  intro K _ g H σ hne
  refine ⟨cramerTri H σ, cramerTri_blockTriangular H σ, cramerTri_diag H σ, cramerCol_eq_mul H σ, ?_⟩
  change Matrix.det ((rowSel (σ g) : Matrix (Fin g) (Fin (g + g)) K) * cramerCol H σ) = 1
  rw [cramerCol_eq_mul, ← Matrix.mul_assoc, Matrix.det_mul,
    Matrix.det_of_upperTriangular (cramerTri_blockTriangular H σ), rowSel_mul_det]
  simp_rw [cramerTri_diag]
  set f : ℕ → K := fun k => if h : k ≤ g then minorAt H k h (σ k) else 1 with hfdef
  have hf : ∀ k, k ≤ g → f k ≠ 0 := fun k hk => by simp only [hfdef, dif_pos hk]; exact hne k hk
  have hterm : ∀ k : Fin g, minorAt H k k.2.le (σ k) / minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) =
      f k / f ((k : ℕ) + 1) := fun k => by
    simp only [hfdef, dif_pos k.2.le, dif_pos (show (k : ℕ) + 1 ≤ g from k.2)]
  simp_rw [hterm]
  rw [Fin.prod_univ_eq_prod_range (fun k => f k / f (k + 1)) g, prod_range_telescope f g hf g le_rfl]
  have hg : minorAt H g le_rfl (σ g) = f g := by simp only [hfdef, dif_pos (le_refl g)]
  have h0 : f 0 = 1 := by simp only [hfdef, dif_pos (Nat.zero_le g)]; exact minorAt_zero H (σ 0)
  rw [hg, h0, mul_one_div_cancel (hf g le_rfl)]

end GlobalTheory.WholeFlag.Glue

end
