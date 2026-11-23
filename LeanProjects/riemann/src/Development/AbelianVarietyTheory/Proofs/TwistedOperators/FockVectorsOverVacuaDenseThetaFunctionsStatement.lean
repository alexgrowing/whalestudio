import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions : ∀ D : D7, GlobalTheory.ChainFr.FockDense D := by
  first | exact @GlobalTheory.FockDensity.fockDense | exact GlobalTheory.FockDensity.fockDense | (intros; apply GlobalTheory.FockDensity.fockDense <;> assumption)
