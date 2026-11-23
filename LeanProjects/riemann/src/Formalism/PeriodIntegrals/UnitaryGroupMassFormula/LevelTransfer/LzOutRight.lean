import Mathlib
import Formalism.FormalDegreeBessel.StatementRP

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants

variable {k i r' : ℕ}

theorem lev_val (j : Fin (2 * r' + k + 1)) : (levPos k i r' j).val = j.val + i := rfl

theorem lev_inj : Function.Injective (levPos k i r') := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [lev_val, lev_val] at h'
  omega

theorem liftVec_lev (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k i r' v (levPos k i r' j) = v j := by
  have hj := j.isLt
  have h1 : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  show j.val + i - i = j.val
  omega

theorem liftVec_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by
  simp only [liftVec]
  rw [dif_neg hp]

theorem ιLev_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g (levPos k i r' p) (levPos k i r' q) = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  have h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext
  · show p.val + i - i = p.val
    omega
  · show q.val + i - i = q.val
    omega

theorem ιLev_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]

theorem ιLev_in_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]

theorem sum_lev {M : Type*} [AddCommMonoid M] (f : Fin (2 * (i + r') + k + 1) → M)
    (h : ∀ p : Fin (2 * (i + r') + k + 1), ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → f p = 0) :
    ∑ p, f p = ∑ j : Fin (2 * r' + k + 1), f (levPos k i r' j) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := levPos k i r') (fun x _ y _ e => lev_inj e)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  apply h
  intro hc
  apply hp
  refine Finset.mem_image.2 ⟨⟨p.val - i, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  show p.val - i + i = p.val
  omega

theorem hpk_lev (p q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' p) (levPos k i r' q) = Hpk k r' p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, lev_val]
  have e1 : (↑p + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑p < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (↑q + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑q < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (i + r' ≤ p.val + i ∧ p.val + i ≤ i + r' + k ∧ p.val + i = q.val + i) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (↑p + i = i + r' + k) ↔ (↑p = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

theorem hpk_in_out (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_out_in (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) (hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) :
    Hpk k (i + r') p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

def Lz (k i r' : ℕ) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ := fun p q =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then
    (if hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i then X ⟨p.val - i, by omega⟩ ⟨q.val - i, by omega⟩ else 0)
  else 0

theorem ιLev_eq (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' X = Lz k i r' X + ιLev k i r' 0 := by
  ext p q
  simp only [ιLev, Lz, Matrix.add_apply]
  split_ifs <;> simp

theorem Lz_lev (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    Lz k i r' X (levPos k i r' p) (levPos k i r' q) = X p q := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  have h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [Lz]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext
  · show p.val + i - i = p.val
    omega
  · show q.val + i - i = q.val
    omega

theorem Lz_out_left (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : Lz k i r' X p q = 0 := by
  simp only [Lz]
  rw [dif_neg hp]

theorem Lz_out_right (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : Lz k i r' X p q = 0 := by
  simp only [Lz]
  split_ifs <;> first | rfl | (exfalso; apply hq; assumption)

def LzL (k i r' : ℕ) :
    Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ →ₗ[ℂ]
      Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ where
  toFun := Lz k i r'
  map_add' X Y := by
    ext p q; simp only [Lz, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext p q; simp only [Lz, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem LzL_apply (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) : LzL k i r' X = Lz k i r' X := rfl

section Hom

variable (hL : LevHom)
include hL

theorem Lz_mul (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X * Y) = Lz k i r' X * Lz k i r' Y := by
  ext p q
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
    · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
        ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
      obtain ⟨b, rfl⟩ : ∃ b, levPos k i r' b = q :=
        ⟨⟨q.val - i, by omega⟩, Fin.ext (by show q.val - i + i = q.val; omega)⟩
      rw [Lz_lev, Matrix.mul_apply, Matrix.mul_apply, sum_lev]
      · simp only [Lz_lev]
      · intro m hm
        rw [Lz_out_right _ _ _ hm, zero_mul]
    · rw [Lz_out_right _ _ _ hq, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_right _ _ _ hq, mul_zero]).symm
  · rw [Lz_out_left _ _ _ hp, Matrix.mul_apply]
    exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_left _ _ _ hp, zero_mul]).symm

theorem Lz_one : Lz k i r' 1 + ιLev k i r' 0 = 1 := by
  rw [← ιLev_eq]
  exact (hL k i r').1

theorem Lz_pow (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (n : ℕ) :
    Lz k i r' (X ^ (n + 1)) = Lz k i r' X ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, Lz_mul hL, ih, ← pow_succ]

end Hom

end PIQnLT
