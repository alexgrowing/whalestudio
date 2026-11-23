import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem stepBoundAt_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ)
    (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B Cg n₀ d p q b hn₀ hC
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  have hK := countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hC
  obtain ⟨hD, -, -, -, -, -, -, -, hlam, -⟩ := hC
  refine GlobalTheory.StepGlob.stepBoundAt_of_local B b (fun v => ?_)
  obtain ⟨hpar, hds, -, -⟩ := hD v
  have hU : IsURepOn (UJset (B.I.ε v)) (B.σ v) := hds.2.2.1
  have h120v : 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hrk v]; exact h120
  have heig := GlobalTheory.T.lowestKType_infinitesimalChar_large_gap B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hpar hds h (hgap v) h120v
  exact ⟨hU, GlobalTheory.StepBoundOneRep.stepBound_of_eigen B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) b hU
    (hK v) heig (hlam v)⟩

end GlobalTheory.Dec
