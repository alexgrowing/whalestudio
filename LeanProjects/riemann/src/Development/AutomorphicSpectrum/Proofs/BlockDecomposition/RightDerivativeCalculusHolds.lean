import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rcalc : RCalc := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ f hf
    exact ⟨fun X => Rd_contDiffOn X hf, fun X Y g hg => Rd_bracket X Y hf hg, fun s m X g hg => Rd_gel X s m hf hg,
      fun s m x hx g hg => ⟨gel_left s m hx hf hg, gel_right s m hx hf hg⟩⟩
  · intro E f hf s m
    exact gel_mem_CE E hf s m
  · intro _ _ μ _ V _ _ _ f hf hc X
    exact ibp n μ V f hf hc X

end GlobalTheory.CompanionTheory.RCalc
