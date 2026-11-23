import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem exists_inv_frame_of_posDef {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ X : Matrix n n ℂ, IsUnit X.det ∧ (X⁻¹).conjTranspose * X⁻¹ = A := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBdet, hB, Matrix.star_eq_conjTranspose]

theorem exists_isFrames (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (h : ∀ v : InfinitePlace K, ((Df.HV Bs.μ0).map v.embedding).PosDef) : ∃ X0, IsFrames Df X0 := by
  choose X hX using fun v => exists_inv_frame_of_posDef _ (h v)
  exact ⟨X, hX⟩

end GlobalTheory.ColRows
