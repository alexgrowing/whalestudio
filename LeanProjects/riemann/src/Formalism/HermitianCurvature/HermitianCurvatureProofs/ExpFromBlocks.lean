import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def fbHom (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix m m ℂ × Matrix n n ℂ →+* Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' p q := by simp [Matrix.fromBlocks_add]

set_option backward.isDefEq.respectTransparency false in
theorem exp_reindex (e : m ≃ n) (M : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e M) = Matrix.reindex e e (NormedSpace.exp M) := by
  have hc : Continuous fun M : Matrix m m ℂ => Matrix.reindexAlgEquiv ℂ ℂ e M := by
    simp only [Matrix.coe_reindexAlgEquiv]; exact continuous_id.matrix_reindex e e
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc M
  simp only [Matrix.coe_reindexAlgEquiv] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem exp_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) = Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  have hc : Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => fbHom m n p := by
    show Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => Matrix.fromBlocks p.1 0 0 p.2
    exact Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (fbHom m n) hc (A, D)
  open scoped Matrix.Norms.Operator in
  have h1 := Prod.fst_exp (A, D)
  open scoped Matrix.Norms.Operator in
  have h2 := Prod.snd_exp (A, D)
  change Matrix.fromBlocks _ 0 0 _ = NormedSpace.exp (Matrix.fromBlocks _ 0 0 _) at h
  rw [h1, h2] at h
  exact h.symm

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
