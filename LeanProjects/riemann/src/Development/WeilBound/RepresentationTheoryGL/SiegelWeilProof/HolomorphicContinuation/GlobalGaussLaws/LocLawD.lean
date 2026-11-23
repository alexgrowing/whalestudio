import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem mat_mOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (A : GL (Fin n) ℂ) :
    mat (ι (mOf A)) = blk4 (unitAt hσ τ A).1 0 0 (adj ((unitAt hσ τ A)⁻¹).1) := by
  have hU : ((unitAt hσ τ A).1).map (finPart D) = 1 := by
    rw [unitAt_val]
    exact finite_part_adelic_point_matrix hσ τ A.1
  have hUi : (((unitAt hσ τ A)⁻¹).1).map (finPart D) = 1 := finite_part_adelic_point_matrix hσ τ (A⁻¹).1
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 (mOf A)).2.2, finite_part_block_matrix_map, hU, finPart_adj _ hUi, Matrix.map_zero _ (map_zero _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 (mOf A)).1, mR_mOf, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_matrix hσ,
        compAt_zero]
      have hUc : compAt θ τ ((unitAt hσ τ A)⁻¹).1 = (A⁻¹).1 := component_adelic_point_matrix hσ τ (A⁻¹).1
      rw [hUc]
      rfl
    · rw [(hι.2 (mOf A)).2.1 τ' e, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_ne hσ e,
        compAt_zero]
      have hUc : compAt θ τ' ((unitAt hσ τ A)⁻¹).1 = 1 := component_adelic_point_ne hσ e (A⁻¹).1
      rw [hUc, Matrix.conjTranspose_one, block_matrix_diagonal_one_eq_one]

theorem mat_nOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (y : PositivityTheory.Rg.Sw.GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks 1 b 0 1) : mat (ι y) = blk4 1 (atT σ τ b) 0 1 := by
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 y).2.2, finite_part_block_matrix_map, finPart_atT_map hσ τ b, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 y).1, hy, component_block_matrix (R := ℂ), compAt_one, compAt_atT hσ, compAt_zero]
      rfl
    · rw [(hι.2 y).2.1 τ' e, component_block_matrix (R := ℂ), compAt_one, compAt_atT_ne hσ e, compAt_zero, block_matrix_diagonal_one_eq_one]

end PositivityTheory.Rg.Sw.Glob.LocLawH
