import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualElement_standardChar_splitPrime : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (e₁ : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e₁ PP → ∃ c : Datum.EAf D, (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 → toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧ (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  first | exact @GlobalTheory.SplitDualElt.exists_dual_elt | exact GlobalTheory.SplitDualElt.exists_dual_elt | (intros; apply GlobalTheory.SplitDualElt.exists_dual_elt <;> assumption)
