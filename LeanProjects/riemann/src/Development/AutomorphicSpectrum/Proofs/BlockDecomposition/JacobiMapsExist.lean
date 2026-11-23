import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.JacobiMaps

variable {D : D7} {n ρ p : ℕ}

section Bl

variable {R : Type} [CommRing R] (hn : ρ + p = n)

theorem block_mul₂ (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R) (c c' : Matrix (Fin p) (Fin ρ) R)
    (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' = bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  ext i j
  simp only [bl, Matrix.submatrix_apply, Matrix.zero_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem block_sub (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R) (c c' : Matrix (Fin p) (Fin ρ) R)
    (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d - bl hn a' b' c' d' = bl hn (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  simp only [bl, Matrix.submatrix_apply, Matrix.sub_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem bl_add (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R) (c c' : Matrix (Fin p) (Fin ρ) R)
    (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  ext i j
  simp only [bl, Matrix.submatrix_apply, Matrix.add_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem block_neg (a : Matrix (Fin ρ) (Fin ρ) R) (b : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) : -bl hn a b c d = bl hn (-a) (-b) (-c) (-d) := by
  ext i j
  simp only [bl, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem blockMatrix_neg_one : bl hn (-1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (-1) = -1 := by
  have h := block_sub hn (0 : Matrix (Fin ρ) (Fin ρ) R) 1 0 0 0 0 (0 : Matrix (Fin p) (Fin p) R) 1
  rw [blockMatrix_zero, blockRowSubstitution_one] at h
  simpa using h.symm

theorem sh_mul (y y' : Matrix (Fin ρ) (Fin p) R) (h : y' = -y) :
    bl hn 1 y 0 1 * bl hn 1 y' 0 1 = (1 : Matrix (Fin n) (Fin n) R) := by
  subst h
  simp only [block_mul₂, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, add_neg_cancel,
    neg_add_cancel]
  exact blockRowSubstitution_one (R := R) hn

theorem wM_mul : blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1) *
    blk4 (bl hn 0 0 0 1) (bl hn (-1) 0 0 0) (bl hn 1 0 0 0) (bl hn 0 0 0 1) =
      (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  have z : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := blockRowSubstitution_one hn
  simp only [submatrix_fromBlocks_mul, block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero, neg_neg, z, o, block_matrix_one]

theorem wM_mul' : blk4 (bl hn 0 0 0 1) (bl hn (-1) 0 0 0) (bl hn 1 0 0 0) (bl hn 0 0 0 1) *
    blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1) =
      (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  have z : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := blockRowSubstitution_one hn
  simp only [submatrix_fromBlocks_mul, block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero, neg_neg, z, o, block_matrix_one]

theorem wM_form : blk4 (bl hn 0 0 0 1) (bl hn (-1) 0 0 0) (bl hn 1 0 0 0) (bl hn 0 0 0 1) * blk4 0 1 (-1) 0 *
    blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1) =
      (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  have z : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (-1 : Matrix (Fin p) (Fin p) R) = -1 := blockMatrix_neg_one hn
  simp only [submatrix_fromBlocks_mul, block_mul₂, bl_add, block_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, neg_zero, neg_neg, z, o, m]

end Bl

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

section Blocks

variable {R : Type}

def b11 (M : Matrix (Fin (p + p)) (Fin (p + p)) R) : Matrix (Fin p) (Fin p) R :=
  M.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inl i))

def b12 (M : Matrix (Fin (p + p)) (Fin (p + p)) R) : Matrix (Fin p) (Fin p) R :=
  M.submatrix (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inr i))

def b21 (M : Matrix (Fin (p + p)) (Fin (p + p)) R) : Matrix (Fin p) (Fin p) R :=
  M.submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun i => finSumFinEquiv (Sum.inl i))

def b22 (M : Matrix (Fin (p + p)) (Fin (p + p)) R) : Matrix (Fin p) (Fin p) R :=
  M.submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun i => finSumFinEquiv (Sum.inr i))

theorem block_matrix_of_blocks (M : Matrix (Fin (p + p)) (Fin (p + p)) R) : blk4 (b11 M) (b12 M) (b21 M) (b22 M) = M := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [blk4, b11, b12, b21, b22, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem upperLeft_block (a b c d : Matrix (Fin p) (Fin p) R) : b11 (blk4 a b c d) = a := by
  ext i j
  simp only [blk4, b11, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem upperRight_block (a b c d : Matrix (Fin p) (Fin p) R) : b12 (blk4 a b c d) = b := by
  ext i j
  simp only [blk4, b12, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem lowerLeft_block_entry (a b c d : Matrix (Fin p) (Fin p) R) : b21 (blk4 a b c d) = c := by
  ext i j
  simp only [blk4, b21, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem lowerRight_block (a b c d : Matrix (Fin p) (Fin p) R) : b22 (blk4 a b c d) = d := by
  ext i j
  simp only [blk4, b22, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

variable [TopologicalSpace R] {X : Type} [TopologicalSpace X]

theorem continuous_block_matrix {a b c d : X → Matrix (Fin p) (Fin p) R} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) : Continuous fun x => blk4 (a x) (b x) (c x) (d x) :=
  (ha.matrix_fromBlocks hb hc hd).matrix_submatrix _ _

theorem continuous_bl (hn : ρ + p = n) {a : X → Matrix (Fin ρ) (Fin ρ) R} {b : X → Matrix (Fin ρ) (Fin p) R}
    {c : X → Matrix (Fin p) (Fin ρ) R} {d : X → Matrix (Fin p) (Fin p) R} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) : Continuous fun x => bl hn (a x) (b x) (c x) (d x) :=
  (ha.matrix_fromBlocks hb hc hd).matrix_submatrix _ _

end Blocks

theorem continuous_adjR {a b : ℕ} : Continuous (adj : Mx D a b → Mx D b a) :=
  (continuous_id.matrix_map GlobalTheory.AnnihBox.continuous_cA').matrix_transpose

theorem adjoint_symplectic_block_product (a b c d : Mx D n n) :
    (adj (blk4 a b c d : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 * blk4 a b c d : Mx D (n + n) (n + n)) =
      blk4 (adj a * c - adj c * a) (adj a * d - adj c * b) (adj b * c - adj d * a) (adj b * d - adj d * b) := by
  rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [mul_zero, mul_one, mul_neg, zero_add, add_zero, neg_mul, sub_eq_add_neg]
  congr 1 <;> abel

def mkG (u : GL (Fin (n + n)) (AE D))
    (h : (adj u.1 * blk4 0 1 (-1) 0 * u.1 : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0) : G D n :=
  ⟨u, by
    change adj u.1 * JR (AF D.host.F) (Jst D n) * u.1 = JR (AF D.host.F) (Jst D n)
    rw [JR_Jst]; exact h⟩

theorem mat_mkG (u : GL (Fin (n + n)) (AE D)) (h) : mat (mkG (D := D) u h) = u.1 := rfl

theorem isU_mat (g : G D n) :
    (adj (mat g) * blk4 0 1 (-1) 0 * mat g : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rwa [JR_Jst] at h

theorem continuous_mkG {X : Type} [TopologicalSpace X] {f : X → GL (Fin (n + n)) (AE D)} (hf : Continuous f)
    (h : ∀ x, (adj (f x).1 * blk4 0 1 (-1) 0 * (f x).1 : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0) :
    Continuous fun x => mkG (f x) (h x) :=
  (isEmbedding_matHom _ D.sp.cm.sig (Jst D n)).continuous_iff.2 hf

def nAt (b : Mx D n n) (hb : adj b = b) : G D n :=
  mkG ⟨blk4 1 b 0 1, blk4 1 (-b) 0 1, by simp [submatrix_fromBlocks_mul, block_matrix_one], by simp [submatrix_fromBlocks_mul, block_matrix_one]⟩ (by
    simp only [adjoint_symplectic_block_product, adj_one, adj_zero, hb, mul_zero, zero_mul, mul_one, one_mul, sub_zero, sub_self, zero_sub])

theorem mat_nAt (b : Mx D n n) (hb : adj b = b) : mat (nAt b hb) = blk4 1 b 0 1 := rfl

theorem continuous_nAt {X : Type} [TopologicalSpace X] {f : X → Mx D n n} (hf : Continuous f)
    (h : ∀ x, adj (f x) = f x) : Continuous fun x => nAt (f x) (h x) := by
  refine continuous_mkG (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_block_matrix continuous_const hf continuous_const continuous_const
  · exact continuous_block_matrix continuous_const hf.neg continuous_const continuous_const

def mAt (a a' : Mx D n n) (h1 : a * a' = 1) (h2 : a' * a = 1) : G D n :=
  mkG ⟨blk4 a 0 0 (adj a'), blk4 a' 0 0 (adj a), by
      have e : (adj a' * adj a : Mx D n n) = 1 := by rw [← adj_mul, h1, adj_one]
      simp [submatrix_fromBlocks_mul, block_matrix_one, h1, e], by
      have e : (adj a * adj a' : Mx D n n) = 1 := by rw [← adj_mul, h2, adj_one]
      simp [submatrix_fromBlocks_mul, block_matrix_one, h2, e]⟩ (by
    have e : (adj a * adj a' : Mx D n n) = 1 := by rw [← adj_mul, h2, adj_one]
    have e' : (adj (adj a') * a : Mx D n n) = 1 := by rw [adj_adj, h2]
    simp only [adjoint_symplectic_block_product, adj_zero, mul_zero, zero_mul, sub_zero, sub_self, zero_sub, e, e'])

theorem mat_mAt (a a' : Mx D n n) (h1 h2) : mat (mAt a a' h1 h2) = blk4 a 0 0 (adj a') := rfl

theorem continuous_mAt {X : Type} [TopologicalSpace X] {a a' : X → Mx D n n} (ha : Continuous a) (ha' : Continuous a')
    (h1 : ∀ x, a x * a' x = 1) (h2 : ∀ x, a' x * a x = 1) : Continuous fun x => mAt (a x) (a' x) (h1 x) (h2 x) := by
  refine continuous_mkG (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_block_matrix ha continuous_const continuous_const (continuous_adjR.comp ha')
  · exact continuous_block_matrix ha' continuous_const continuous_const (continuous_adjR.comp ha)

def embM (hn : ρ + p = n) (M : Mx D (p + p) (p + p)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn 1 0 0 (b11 M)) (bl hn 0 0 0 (b12 M)) (bl hn 0 0 0 (b21 M)) (bl hn 1 0 0 (b22 M))

theorem block_embedding_block_matrix (hn : ρ + p = n) (a b c d : Mx D p p) :
    embM hn (blk4 a b c d) = blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) := by
  rw [embM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def embMon (hn : ρ + p = n) : Mx D (p + p) (p + p) →* Mx D (n + n) (n + n) where
  toFun := embM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := p), block_embedding_block_matrix, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, block_embedding_block_matrix, block_embedding_block_matrix, block_embedding_block_matrix, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem embM_isU (hn : ρ + p = n) (M : Mx D (p + p) (p + p))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (p + p) (p + p)) = blk4 0 1 (-1) 0) :
    (adj (embM hn M) * blk4 0 1 (-1) 0 * embM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [block_embedding_block_matrix, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def embF (hn : ρ + p = n) (g : G D p) : G D n :=
  mkG (Units.map (embMon hn) (matHom _ D.sp.cm.sig (Jst D p) g)) (embM_isU hn _ (isU_mat g))

theorem matHom_embF (hn : ρ + p = n) (g : G D p) :
    matHom _ D.sp.cm.sig (Jst D n) (embF hn g) = Units.map (embMon hn) (matHom _ D.sp.cm.sig (Jst D p) g) := rfl

def embG (hn : ρ + p = n) : G D p →* G D n where
  toFun := embF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_embF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_embF, matHom_embF, matHom_embF, map_mul, map_mul])

theorem mat_embG (hn : ρ + p = n) (h : G D p) : mat (embG hn h) = embM hn (mat h) := rfl

theorem continuous_embM (hn : ρ + p = n) : Continuous (embM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn continuous_const continuous_const continuous_const
      (continuous_id.matrix_submatrix _ _))
    (continuous_bl hn continuous_const continuous_const continuous_const (continuous_id.matrix_submatrix _ _))
    (continuous_bl hn continuous_const continuous_const continuous_const (continuous_id.matrix_submatrix _ _))
    (continuous_bl hn continuous_const continuous_const continuous_const (continuous_id.matrix_submatrix _ _))

theorem continuous_embG (hn : ρ + p = n) : Continuous (embG (D := D) hn) := by
  have h0 : Continuous (Units.map (embMon (D := D) hn : Mx D (p + p) (p + p) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_embM hn)
  have h : Continuous fun g : G D p => Units.map (embMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D p) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

theorem herm_bl (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) :
    adj (bl hn z.1 x (adj x) 0 : Mx D n n) = bl hn z.1 x (adj x) 0 := by
  have hz : adj z.1 = z.1 := z.2
  rw [adj_bl, adj_adj, adj_zero, hz]

theorem exists_w (D : D7) {n ρ p : ℕ} (hn : ρ + p = n) : ∃ g : G D n,
    mat g = blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1) := by
  refine exists_mat _ (blk4 (bl hn 0 0 0 1) (bl hn (-1) 0 0 0) (bl hn 1 0 0 0) (bl hn 0 0 0 1)) (wM_mul hn) (wM_mul' hn) ?_
  rw [adelicConjTranspose_blockMatrixTwoByTwoFin]
  simp only [adj_bl, adj_one, adj_zero, adj_neg]
  exact wM_form hn

def nzxF (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) : G D n :=
  nAt (bl hn z.1 x (adj x) 0) (herm_bl hn z x)

theorem continuous_nzxF (hn : ρ + p = n) : Continuous fun u : hermA D ρ × Mx D ρ p => nzxF (D := D) hn u.1 u.2 :=
  continuous_nAt (f := fun u : hermA D ρ × Mx D ρ p => (bl hn u.1.1 u.2 (adj u.2) 0 : Mx D n n))
    (continuous_bl hn (continuous_subtype_val.comp continuous_fst) continuous_snd
      (continuous_adjR.comp continuous_snd) continuous_const) _

def shF (hn : ρ + p = n) (y : Mx D ρ p) : G D n :=
  mAt (bl hn 1 y 0 1) (bl hn 1 (-y) 0 1) (sh_mul hn _ _ rfl) (sh_mul hn _ _ (neg_neg y).symm)

theorem continuous_shF (hn : ρ + p = n) : Continuous (shF (D := D) hn) :=
  continuous_mAt (a := fun y : Mx D ρ p => (bl hn 1 y 0 1 : Mx D n n))
    (a' := fun y : Mx D ρ p => (bl hn 1 (-y) 0 1 : Mx D n n))
    (continuous_bl hn continuous_const continuous_id continuous_const continuous_const)
    (continuous_bl hn continuous_const continuous_neg continuous_const continuous_const) _ _

theorem mat_shF (hn : ρ + p = n) (y : Mx D ρ p) :
    mat (shF hn y : G D n) = blk4 (bl hn 1 y 0 1) 0 0 (bl hn 1 0 (-adj y) 1) := by
  have e : adj (bl hn 1 (-y) 0 1 : Mx D n n) = bl hn 1 0 (-adj y) 1 := by
    rw [adj_bl, adj_neg]
    simp only [adj_one, adj_zero]
  exact (mat_mAt _ _ _ _).trans (congrArg (blk4 (bl hn 1 y 0 1) 0 0) e)

theorem embedded_block_matrix_form (hn : ρ + p = n) (h : G D p) (a b c d : Mx D p p) (e : mat h = blk4 a b c d) :
    mat (embG hn h) = blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) :=
  (mat_embG hn h).trans ((congrArg (embM hn) e).trans (block_embedding_block_matrix hn a b c d))

def maps (D : D7) {n ρ p : ℕ} (hn : ρ + p = n) : Maps D hn where
  emb := embG hn
  nzx := nzxF hn
  sh := shF hn
  w := (exists_w D hn).choose
  emb_cont := continuous_embG hn
  nzx_cont := continuous_nzxF hn
  sh_cont := continuous_shF hn
  emb_mat := embedded_block_matrix_form hn
  nzx_mat _ _ := rfl
  sh_mat := mat_shF hn
  w_mat := (exists_w D hn).choose_spec

theorem mapsExist : MapsExist := by
  intro D n ρ p hn
  obtain ⟨lam, 𝓖, hz⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D ρ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D ρ p
  exact ⟨⟨maps D hn⟩, ⟨⟨lam, 𝓖, μ, 𝓕, hz, hμ⟩⟩⟩

end GlobalTheory.CompanionTheory.JacobiMaps

end
