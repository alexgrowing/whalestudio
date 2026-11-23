import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeLevelEqUnitaryInfFrameStabilizer
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLevel_eq_unitary_inf_frame_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → GlobalTheory.Mass.Levels.latLev V = Formalism.L2.DIV.UA D.sp.cm V.gram ⊓ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LatLevEq.latLev_eq_UA_inf_St | exact GlobalTheory.LatLevEq.latLev_eq_UA_inf_St | (intros; apply GlobalTheory.LatLevEq.latLev_eq_UA_inf_St <;> assumption)
