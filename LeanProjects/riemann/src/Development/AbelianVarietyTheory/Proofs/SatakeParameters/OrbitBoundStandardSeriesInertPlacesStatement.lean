import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitBound_standardSeries_inertPlaces : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Ee : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X Ee → (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, Ee.row u i (false, t) 0 - Ee.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 → BeFam D Ee.ep Ee.be → (Ee.sg = fun _ _ => -1) → OrbitPlaces.OrbitBoundWithoutOperator Ee X K := by
  first | exact @GlobalTheory.OrbitBoundStdRec.orbit_bound_rec | exact GlobalTheory.OrbitBoundStdRec.orbit_bound_rec | (intros; apply GlobalTheory.OrbitBoundStdRec.orbit_bound_rec <;> assumption)
