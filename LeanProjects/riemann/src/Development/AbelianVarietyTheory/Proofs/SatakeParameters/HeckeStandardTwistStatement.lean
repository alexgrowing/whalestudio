import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeStandardTwist
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_standard_twist : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), HeckeStdTw P.H.cover.B := by
  first | exact @GlobalTheory.NPin.heckeStdTw_cover | exact GlobalTheory.NPin.heckeStdTw_cover | (intros; apply GlobalTheory.NPin.heckeStdTw_cover <;> assumption)
