import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) K) 0 0 1 = 1 := by
  simp [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem neg_block_matrix {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_neg]
  rfl

theorem exists_blockMatrixTwoByTwoFin_eq {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    ∃ A B C D : Matrix (Fin n) (Fin n) K, g = blk4 A B C D := by
  refine ⟨(g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem is_siegel_parabolic_block_iff {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 a b c d) ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    have h' := h i j
    simpa only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using h'
  · rintro rfl i j
    simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]

theorem det_block_lower_zero {n : ℕ} (a b d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b 0 d).det = a.det * d.det := by
  simp only [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

section cT
variable (σ : K →+* K)

theorem cT_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  unfold cT; simp

theorem cT_zero {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  unfold cT; simp

theorem cT_neg {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_sub {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

theorem det_cT {a : ℕ} (x : Matrix (Fin a) (Fin a) K) : (cT σ x).det = σ x.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_cT {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : IsUnit (cT σ x).det := by
  rw [det_cT]; exact hx.map σ

theorem cT_inv {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : cT σ x⁻¹ = (cT σ x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hx, cT_one]

theorem cT_blk4 {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end cT

theorem Jm_mul_Jm (n : ℕ) : Jm K n * Jm K n = -1 := by
  rw [Jm, submatrix_fromBlocks_mul, ← block_matrix_one (K := K), neg_block_matrix]
  congr 1 <;> simp

theorem unitary_left_inv (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : (-(Jm K n * cT σ g * Jm K n)) * g = 1 := by
  unfold IsUnitary at hg
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g), hg, Jm_mul_Jm, neg_neg]

theorem isUnit_det_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (unitary_left_inv σ hg)

theorem inv_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : g⁻¹ = -(Jm K n * cT σ g * Jm K n) :=
  Matrix.inv_eq_left_inv (unitary_left_inv σ hg)

theorem unitary_mul (σ : K →+* K) {N : ℕ} {J g h : Matrix (Fin N) (Fin N) K}
    (hg : IsUnitary σ J g) (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul, show cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h by
    simp only [Matrix.mul_assoc], hg, hh]

section eId

theorem eId_mul_eId (n r : ℕ) : eId K n r * eId K n r = eId K n r := by
  rw [eId, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem cT_eId (σ : K →+* K) (n r : ℕ) : cT σ (eId K n r) = eId K n r := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, eId, Matrix.diagonal_apply, apply_ite σ]
  · simp [cT, eId, Matrix.diagonal_apply, h, Ne.symm h]

theorem eId_mul_extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : eId K n r * extB b = extB b := by
  ext i j
  simp only [eId, Matrix.diagonal_mul, extB]
  split_ifs <;> simp_all

theorem extB_mul_eId {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : extB b * eId K n r = extB b := by
  ext i j
  simp only [eId, Matrix.mul_diagonal, extB]
  split_ifs <;> simp_all

theorem cT_extB (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    cT σ (extB (n := n) b) = extB (cT σ b) := by
  ext i j
  simp only [cT, extB, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp_all

theorem extB_injective {n r : ℕ} (hr : r ≤ n) {b b' : Matrix (Fin r) (Fin r) K}
    (h : extB (n := n) b = extB b') : b = b' := by
  ext i j
  have h' := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  simpa [extB] using h'

end eId

theorem repMat_eq (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    repMat σ b a = blk4 ((1 - eId K n r) * a) (eId K n r * (cT σ a)⁻¹) (-(eId K n r * a))
      ((1 - eId K n r - extB b) * (cT σ a)⁻¹) := by
  rw [repMat, wr, nB, mA, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  congr 1 <;> simp [sub_mul, mul_sub, add_mul, eId_mul_extB] <;> abel

end GlobalTheory.CompanionTheory.BruhatCell
