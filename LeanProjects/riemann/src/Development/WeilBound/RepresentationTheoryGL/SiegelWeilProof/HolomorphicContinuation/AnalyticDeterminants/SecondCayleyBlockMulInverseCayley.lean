import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Cmi (n : ℕ) : M2 n :=
  fromBlocks ((-Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1) ((Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1)

theorem cm_mul_cmi : Cm n * Cmi n = 1 := by
  rw [Cm, Cmi, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem cm_inv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv cm_mul_cmi

theorem toBlocks₂₁_mul (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₂₂_mul (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₂₁ (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by
  rw [toBlocks₂₁_mul, u1, Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one]

theorem mul_cm₂₂ (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by
  rw [toBlocks₂₂_mul, u2, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]

theorem first_cayley_block_mul_inverse_cayley (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by
  rw [u1, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem second_cayley_block_mul_inverse_cayley (y : M2 n) : u2 (y * Cmi n) = y.toBlocks₂₂ := by
  rw [u2, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem uAct : UAct := by
  intro n x P Q R S
  simp only [mX, cm_inv, ← Matrix.mul_assoc]
  rw [first_cayley_block_mul_inverse_cayley, second_cayley_block_mul_inverse_cayley, toBlocks₂₁_mul (x * Cm n) (fromBlocks P Q R S),
    toBlocks₂₂_mul (x * Cm n) (fromBlocks P Q R S), mul_cm₂₁, mul_cm₂₂]
  simp

def incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := Matrix.of fun c i => if c = (i : Fin n) then 1 else 0

def subOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ :=
  M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))

theorem minorOn_eq (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : minorOn s M = (subOn s M).det := rfl

theorem sum_incl (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro i _ hi
      have : a ≠ (i : Fin n) := fun e => hi (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : a ≠ (i : Fin n) := fun e => h (e ▸ i.2)
    simp [this]

theorem embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]
  simp only [sum_incl]
  simp only [mul_comm _ (ite (b = _) _ _)]
  rw [sum_incl]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [embOn, ha, hb]

theorem incl_mul (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : (incl s)ᵀ * M * incl s = subOn s M := by
  ext i j
  simp [Matrix.mul_apply, incl, subOn, Matrix.transpose_apply]

theorem det_one_add_mul_embOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by
  rw [embOn_eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.det_one_add_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [incl_mul]

theorem detD_const_mul {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (F : Matrix ι ι ℂ → ℂ) :
    detD (fun S => c * F S) = c * detD F := by
  by_cases hc : c = 0
  · subst hc
    simp [detD]
  · let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc)
    have hfun : (fun S => c * F S) = g ∘ F := by
      funext S
      simp [g, mul_comm]
    unfold detD
    rw [hfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    (simp [g]) <;> ring

theorem card_blkA {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe, blkA, Fin.card_filter_val_lt, min_eq_right hj]

theorem card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, card_blkA hj]

theorem scalar_section_mul_block_unipotent {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by
  have hd1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hd2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have k1 : u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u1 x * (1 + (wM x)⁻¹ * embOn (blkB j) S) := by
    rw [(uAct n x _ _ _ _).1, wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd2]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd1, Matrix.one_mul,
      Matrix.mul_one]
  have k2 : u2 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u2 x * (1 + wM x * embOn (blkA j) T) := by
    rw [(uAct n x _ _ _ _).2, wM]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [f0, f0, k1, k2, Matrix.det_mul, Matrix.det_mul, det_one_add_mul_embOn, det_one_add_mul_embOn,
    mul_zpow, mul_zpow]
  ring

theorem djSec_of (hC : Cayley) : DjSec := by
  intro n j p q x hj h1 h2
  have hin : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
      (f0 p q x * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) * minorOn (blkB j) (wM x)⁻¹) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-q) := by
    intro T
    simp_rw [scalar_section_mul_block_unipotent h1 h2 T]
    rw [detD_const_mul, hC, card_blkB hj, minorOn_eq]
    push_cast
    ring
  simp_rw [hin]
  rw [detD_const_mul, hC, card_blkA hj]
  simp only [minorOn_eq]
  push_cast
  ring

end PositivityTheory.Rg.Sw.LVs
