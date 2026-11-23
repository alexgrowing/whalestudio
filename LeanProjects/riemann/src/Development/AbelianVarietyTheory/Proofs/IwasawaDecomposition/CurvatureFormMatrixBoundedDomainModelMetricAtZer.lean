import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply

set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial Filter Topology ComplexConjugate
open GlobalTheory.HermFrame

namespace GlobalTheory.DomainDens

variable {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)

def flatCoordinateMatrixBlock (u : ReciprocityTheory.L2DbarEstimates.V n) : Matrix (Fin p) (Fin q) ℂ :=
  Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ

theorem block_reshape_apply (u : ReciprocityTheory.L2DbarEstimates.V n) (i : Fin p) (b : Fin q) :
    flatCoordinateMatrixBlock h τ u i b = u (Fintype.equivFinOfCardEq h (τ, i, b)) := rfl

theorem flatCoordinateMatrixBlock_entry_eq_proj (i : Fin p) (b : Fin q) :
    (fun u => flatCoordinateMatrixBlock h τ u i b) = fun u => EuclideanSpace.proj (𝕜 := ℂ) (Fintype.equivFinOfCardEq h (τ, i, b)) u :=
  rfl

theorem flatCoordinateMatrixBlock_at_zero : flatCoordinateMatrixBlock h τ 0 = 0 := by
  ext i b; simp [block_reshape_apply]

theorem matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (flatCoordinateMatrixBlock h τ) x ξ = flatCoordinateMatrixBlock h τ ξ := by
  ext i b
  rw [mdel_apply, flatCoordinateMatrixBlock_entry_eq_proj, del_eq_fderiv (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  rfl

theorem matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (flatCoordinateMatrixBlock h τ) x η = 0 := by
  ext i b
  rw [mdbar_apply, flatCoordinateMatrixBlock_entry_eq_proj, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem matrixEntriesContDiffAt_flatCoordinateMatrixBlock {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) : MContDiffAt k (flatCoordinateMatrixBlock h τ) x :=
  fun i b => by
    rw [flatCoordinateMatrixBlock_entry_eq_proj]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := k)
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) (Fintype.equivFinOfCardEq h (τ, i, b)) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ)).restrict_scalars ℝ |>.contDiffAt

theorem mContDiffAt_hP {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x := by
  unfold Formalism.DegreeFormula.hP
  exact (mContDiffAt_const 1).sub ((matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).mul (matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).conjTranspose)

theorem mdel_hP (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x ξ = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ) := by
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) x := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x
  have e : (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) =
      fun u => (fun _ => (1 : Matrix (Fin p) (Fin p) ℂ)) u + -(flatCoordinateMatrixBlock h τ u * (flatCoordinateMatrixBlock h τ u)ᴴ) := by
    funext u; simp [Formalism.DegreeFormula.hP, sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (hz.mul hz.conjTranspose).neg, mdel_const, mdel_neg,
    mdel_mul hz hz.conjTranspose, mdel_conjTranspose, matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock]
  simp

theorem hP_zero : Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0) = 1 := by simp [Formalism.DegreeFormula.hP, flatCoordinateMatrixBlock_at_zero]

theorem conn_model (x ξ : ReciprocityTheory.L2DbarEstimates.V n) (hu : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x)).det) :
    conn (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) x ξ =
      flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ * (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x))⁻¹ := by
  rw [conn, transpose_transpose, mdel_transpose (fun u => (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹), transpose_transpose,
    mdel_inv (mContDiffAt_hP h τ x) hu, nonsing_inv_nonsing_inv _ hu, mdel_hP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

theorem curv_model (ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 ξ η = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ η)ᴴ) := by
  have hu0 : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0)).det := by simp [hP_zero]
  have hev := (mContDiffAt_hP (k := 1) h τ 0).eventually_isUnit hu0
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) 0 := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ 0
  rw [curv, mdbar_congr (hev.mono fun x hx => conn_model h τ x ξ hx),
    mdbar_mul ((mContDiffAt_const _).mul hz.conjTranspose) ((mContDiffAt_hP h τ 0).inv hu0),
    mdbar_mul (mContDiffAt_const _) hz.conjTranspose, mdbar_conjTranspose, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock, mdbar_const, hP_zero,
    flatCoordinateMatrixBlock_at_zero]
  simp

theorem curvPoly_model_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι),
    GlobalTheory.GoodMetric.curvPoly
      (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 =
      -GlobalTheory.DomainDens.blockSym h τ := by
  intro ι _ p q n h τ
  have e2 : ∀ (a c : Fin n) (i j : Fin p),
      curv (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)
        0 (GlobalTheory.GoodMetric.coordVec a) (GlobalTheory.GoodMetric.coordVec c) i j =
      -∑ b : Fin q, (if Fintype.equivFinOfCardEq h (τ, i, b) = a then 1 else 0) *
        (if Fintype.equivFinOfCardEq h (τ, j, b) = c then 1 else 0) := by
    intro a c i j
    change curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 _ _ i j = _
    rw [curv_model h τ, Matrix.neg_apply, mul_apply]
    simp [block_reshape_apply, EuclideanSpace.single_apply]
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, of_apply, e2, Matrix.neg_apply, blockSym_apply]
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, neg_inj, map_sum, Finset.sum_mul, mul_ite, ite_mul, one_mul,
    zero_mul, mul_zero, apply_ite (C : ℂ → MvPolynomial (Fin n × Fin n) ℂ), map_one, map_zero]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq]

end GlobalTheory.DomainDens
