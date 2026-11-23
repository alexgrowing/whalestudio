import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParBasic

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem tl_apply (M : Mt g (a + b)) (i j : Fin a) : tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply (M : Mt g (a + b)) (i j : Fin b) : br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

def blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def ur (a b : ℕ) (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

theorem tl_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : tl a (blkM A B D) = A := by
  ext i j; simp [tl_apply, blkM]

theorem br_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : br a b (blkM A B D) = D := by
  ext i j; simp [br_apply, blkM]

theorem ur_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : ur a b (blkM A B D) = B := by
  ext i j; simp [ur, blkM]

theorem inPar_iff (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have := h ⟨i - a, by omega⟩ ⟨j, hj⟩
    convert this using 2 <;> ext <;> simp
    omega

theorem inPar_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : InPar a (blkM A B D) := by
  rw [inPar_iff]
  intro i j; simp [blkM]

theorem blkM_eq {M : Mt g (a + b)} (h : InPar a M) : blkM (tl a M) (ur a b M) (br a b M) = M := by
  rw [inPar_iff] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkM, tl_apply, br_apply, ur, h]

theorem det_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (blkM A B D).det = A.det * D.det := by
  rw [blkM, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem isUnit_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    IsUnit (blkM A B D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [Matrix.isUnit_iff_isUnit_det, det_blkM, IsUnit.mul_iff]

theorem blkM_mul (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    blkM A B D * blkM A' B' D' = blkM (A * A') (A * B' + B * D') (D * D') := by
  rw [blkM, blkM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [blkM]

theorem isUnit_blocks (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    IsUnit (tl a (x : Mt g (a + b))) ∧ IsUnit (br a b (x : Mt g (a + b))) := by
  rw [← isUnit_blkM _ (ur a b x.val), blkM_eq h]
  exact x.isUnit

theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := blkM_mul (tl a x) (tl a y) (ur a b x) (ur a b y) (br a b x) (br a b y)
  rw [blkM_eq hx, blkM_eq hy] at e
  rw [e]
  exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩

theorem exists_subgroup {G : Type} [Group G] [Finite G] (p : G → Prop) (h1 : p 1)
    (hm : ∀ x y, p x → p y → p (x * y)) : ∃ P : Subgroup G, ∀ x, x ∈ P ↔ p x := by
  have hp : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := fun x hx k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hm _ _ ih hx
  refine ⟨{ carrier := {x | p x}, mul_mem' := fun {x y} => hm x y, one_mem' := h1, inv_mem' := fun {x} hx => ?_ },
    fun x => Iff.rfl⟩
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    have h0 := orderOf_pos x
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  change p x⁻¹
  rw [this]
  exact hp x hx _

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j hj hi =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem card_fibre (h₁ : Gn g a) (h₂ : Gn g b) :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b)) ∧
      tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)).card = g ^ (a * b) := by
  have hc : (Finset.univ : Finset (Matrix (Fin a) (Fin b) (ZMod g))).card = g ^ (a * b) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin b → ZMod g) = _
    simp [pow_mul']
  rw [← hc]
  refine Finset.card_bij (fun x _ => ur a b x.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x hx y hy h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply Units.ext
    rw [← blkM_eq hx.1, ← blkM_eq hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, h]
  · intro B _
    have hu := (isUnit_blkM h₁.val B h₂.val).2 ⟨h₁.isUnit, h₂.isUnit⟩
    refine ⟨hu.unit, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsUnit.unit_spec]
      exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩
    · simp only [IsUnit.unit_spec, ur_blkM]

theorem toG_val {n : ℕ} {M : Mt g n} (h : IsUnit M) : (toG M).val = M := by
  rw [toG, dif_pos h, IsUnit.unit_spec]

theorem card_par :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b))).card =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Gn g a × Gn g b)))
    (f := fun x : Gn g (a + b) => (toG (tl a x.val), toG (br a b x.val))) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (g := fun _ => g ^ (a * b))]
  · simp
  · rintro ⟨h₁, h₂⟩ _
    rw [← card_fibre h₁ h₂, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => and_congr_right fun hx => ?_
    have hu := isUnit_blocks x hx
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := fun _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem isUniUp_mul {n : ℕ} (x y : Mt g n) (hx : IsUniUp x) (hy : IsUniUp y) : IsUniUp (x * y) := by
  intro i j
  refine ⟨fun h => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hx i k).1 hk, zero_mul]
    · rw [(hy k j).1 (h.trans_le (not_lt.1 hk)), mul_zero]
  · rintro rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single i, (hx i i).2 rfl, (hy i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hx i k).1 h, zero_mul]
      · rw [(hy k i).1 h, mul_zero]
    · simp

theorem par_basic : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  intro g _ a b n hn
  subst hn
  exact ⟨exists_subgroup _ (inPar_one _ _) fun x y hx hy => (blocks_mul _ _ hx hy).1,
    exists_subgroup _ (isUniUp_one _) fun x y hx hy => isUniUp_mul _ _ hx hy,
    isUnit_blocks, fun x y hx hy => (blocks_mul x y hx hy).2, card_fibre, card_par⟩

end GlobalTheory.GLm.ParBasic
