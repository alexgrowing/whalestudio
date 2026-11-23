import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterAnnihilatorCompactBox
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_annihilator_compact_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ), ∀ V ∈ nhds (0 : Mx D m n), ∃ K : Set (Mx D n m), IsCompact K ∧ ∀ y : Mx D n m, (∀ ξ ∈ V, ξ.map (infPart D) = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace) = 1) → InBox K y := by
  first | exact @GlobalTheory.MatAnnih.annih_mem_box | exact GlobalTheory.MatAnnih.annih_mem_box | (intros; apply GlobalTheory.MatAnnih.annih_mem_box <;> assumption)
