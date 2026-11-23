import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfSizeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceThetaOfCoreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfThetaStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

theorem refW_of_size : Hypotheses2 → DeepGood → Size → FlatDeg → RefW :=
  fun hP _ hS hF => GlobalTheory.T.reference_weight_of_theta hP hS hF (GlobalTheory.T.reference_theta_of_core hS (GlobalTheory.T.reference_core_of_sum_point hS (GlobalTheory.T.sum_point_of_size hS)))

end GlobalTheory.RefSum
