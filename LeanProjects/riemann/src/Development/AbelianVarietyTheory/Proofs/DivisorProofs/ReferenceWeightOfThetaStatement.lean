import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_weight_of_theta : Hypotheses2 → Size → FlatDeg → RefTheta → RefW := by
  first | exact @GlobalTheory.RefSum.ToWeight.refW_of_refTheta | exact GlobalTheory.RefSum.ToWeight.refW_of_refTheta | (intros; apply GlobalTheory.RefSum.ToWeight.refW_of_refTheta <;> assumption)
