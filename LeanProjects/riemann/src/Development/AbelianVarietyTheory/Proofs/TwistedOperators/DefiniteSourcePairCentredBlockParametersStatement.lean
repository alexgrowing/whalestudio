import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParameters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSource_pair_centred_block_parameters : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ al de : List ℚ, Centred D al [] [] de ∧ parHol D i τ = signed (al ++ []) ([] ++ de) (-(D.hc τ).e i) ∧ parDef D i τ = signed (al ++ block D.R.t ++ de) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  first | exact @GlobalTheory.ArchRec.ParPair.centred_pair | exact GlobalTheory.ArchRec.ParPair.centred_pair | (intros; apply GlobalTheory.ArchRec.ParPair.centred_pair <;> assumption)
