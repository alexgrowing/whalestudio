import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.NormAddLeKur

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {K : Type*} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

def what₂ {m : Type*} (X : Matrix (Fin 4 × n) m K) (b : Fin 4) : Matrix n m K := fun i w => X (b, i) w

theorem blockDiag_mul_apply' {m : Type*} [Fintype m] (P : Matrix n n K) (Q : Matrix (Fin 4 × n) m K)
    (a : Fin 4) (i : n) (w : m) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem mul_bd4_apply {m : Type*} [Fintype m] (X : Matrix m (Fin 4 × n) K) (P : Matrix n n K)
    (x : m) (a : Fin 4) (j : n) : (X * bd4 P) x (a, j) = ∑ k, X x (a, k) * P k j := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem transpose_mul_blockDiag_mul {m m' : Type*} [Fintype m] [Fintype m'] (X : Matrix (Fin 4 × n) m K)
    (Y : Matrix (Fin 4 × n) m' K) (H : Matrix n n K) :
    Xᵀ * bd4 H * Y = ∑ b : Fin 4, (what₂ X b)ᵀ * H * what₂ Y b := by
  ext w w'
  rw [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_bd4_apply]
  simp only [what₂, Matrix.mul_apply, transpose_apply]

theorem blockShift_mul_apply {m : Type*} [Fintype m] (c : Fin 4) (X : Matrix (Fin 4 × n) m K) (b : Fin 4) (i : n)
    (w : m) : ((bmv0 c : Matrix (Fin 4 × n) (Fin 4 × n) K) * X) (b, i) w = if b = 0 then X (c, i) w else 0 := by
  simp only [bmv0, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  by_cases hb : b = 0
  · rw [if_pos hb, Finset.sum_eq_single (c, i)]
    · simp [hb]
    · rintro ⟨b', j⟩ _ hne
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact hne (Prod.ext h1 h2.symm)
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hb h

theorem blockDiag_map' {L : Type*} [CommRing L] (f : K →+* L) (P : Matrix n n K) : (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [bd4, Matrix.map_apply]
  split_ifs <;> simp

theorem bd4_transpose (P : Matrix n n K) : (bd4 P)ᵀ = bd4 Pᵀ := by
  ext x y
  simp only [bd4, transpose_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1

theorem blockDiag_mul' (P Q : Matrix n n K) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [blockDiag_mul_apply']
  simp only [bd4, Matrix.mul_apply]
  split_ifs with h <;> simp

theorem bd4_smul (r : K) (P : Matrix n n K) : bd4 (r • P) = r • bd4 P := by
  ext x y
  simp only [bd4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end Blocks

section Lmat
variable {l : ℕ} [Fact l.Prime] {m m' : Type}

theorem lmat_apply (δ : MaximalUnramifiedExtension l) (A B : Matrix m m' ℚ) (x : m) (y : m') :
    lmat δ A B x y = (A x y : MaximalUnramifiedExtension l) + δ * (B x y : MaximalUnramifiedExtension l) := by
  simp [lmat]

theorem lmat_map_σ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (δ : MaximalUnramifiedExtension l) (hσδ : σ δ = -δ) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map σ = lmat δ A (-B) := by
  ext x y
  simp only [Matrix.map_apply, lmat_apply, map_add, map_mul, map_ratCast, hσδ, Matrix.neg_apply, Rat.cast_neg]
  ring

theorem lmat_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (U₁ U₂ : Matrix m m' ℚ)
    (hU : ∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) (x : m) (y : m') :
    lmat δ U₁ U₂ x y ∈ OO dK δ hδ := by
  rw [lmat_apply]
  exact (OO dK δ hδ).add_mem (ratCast_mem _ (hU x y).1) ((OO dK δ hδ).mul_mem δ_mem (ratCast_mem _ (hU x y).2))

end Lmat

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
