import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Parts

section Field

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem extB_castAdd {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.castAdd s i) (Fin.castAdd s j) = b i j := by
  simp [extB]

theorem extB_natAdd_left {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin s) (j : Fin (r + s)) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.natAdd r i) j = 0 := by
  simp [extB]

theorem extB_natAdd_right {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin (r + s)) (j : Fin s) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) i (Fin.natAdd r j) = 0 := by
  simp [extB]

theorem eId_mul_extB {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    eId K (r + s) r * extB b = extB b := by
  ext i j
  rw [eId, Matrix.diagonal_mul]
  by_cases h : (i : ℕ) < r
  · simp [h]
  · simp [h, extB]

theorem representation_matrix_block_form (σ : K →+* K) {r s : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) K) :
    repMat σ b a = blk4 ((1 - eId K (r + s) r) * a)
        (((1 - eId K (r + s) r) * extB b + eId K (r + s) r) * (cT σ a)⁻¹)
        (-(eId K (r + s) r * a))
        ((1 - eId K (r + s) r - extB b) * (cT σ a)⁻¹) := by
  simp only [repMat, wr, nB, mA]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h : -eId K (r + s) r * extB b + (1 - eId K (r + s) r) * 1 =
      1 - eId K (r + s) r - extB b := by
    rw [Matrix.neg_mul, eId_mul_extB, Matrix.mul_one]
    abel
  rw [h]
  simp

end Field

variable {D : D7}

theorem block_matrix_map {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (a.map (incA D)) (b.map (incA D)) (c.map (incA D)) (d.map (incA D)) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem xPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    xPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y C := by
  ext i j
  simp only [xPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inl j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem yPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    yPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y E' := by
  ext i j
  simp only [yPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inr j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem colJoin_mul_eId {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) :
    (HMul.hMul (colJoin y₁ y₂) ((eId D.host.E (r + s) r).map (incA D)) : Mx D m (r + s)) =
      colJoin y₁ (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]

theorem colJoin_mul_extB {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) (b : Matrix (Fin r) (Fin r) D.host.E) :
    (HMul.hMul (colJoin y₁ y₂) ((extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) : Mx D m (r + s)) =
      colJoin (HMul.hMul y₁ (rat b) : Mx D m r) (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_castAdd, extB_natAdd_left, rat]
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_natAdd_right]

theorem parts : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  intro D m r s b a y₁ y₂
  set e := eId D.host.E (r + s) r with he
  set y : Mx D m (r + s) := colJoin y₁ y₂ with hy
  have hmap : ∀ X : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E,
      X.map (incA D) = (incA D).mapMatrix X := fun _ => rfl
  rw [representation_matrix_block_form, block_matrix_map, xPart_zy_mul, yPart_zy_mul]
  constructor
  · have h1 : (-(e * a)).map (incA D) = -(e.map (incA D) * rat a) := by
      simp only [hmap, map_neg, map_mul]; rfl
    rw [h1, Matrix.mul_neg, ← Matrix.mul_assoc, colJoin_mul_eId]
  · have h2 : ((1 - e - extB b) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) =
        (1 - e.map (incA D) - (extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) *
          rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹ := by
      simp only [hmap, map_sub, map_mul, map_one]; rfl
    rw [h2, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hy, colJoin_mul_eId,
      colJoin_mul_extB, ← colJoin_sub, ← colJoin_sub]
    congr 2
    · simp
    · simp

end GlobalTheory.CompanionTheory.EisUnfold.Parts
