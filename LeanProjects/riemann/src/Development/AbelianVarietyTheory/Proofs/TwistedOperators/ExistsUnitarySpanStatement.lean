import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitarySpan
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
theorem _root_.GlobalTheory.T.exists_unitary_module_onto_span_of_intertwining : ∀ (r s : ℕ) (W U I : Type) [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U] (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), IsGK a → IsUAct b → (∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)) → ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U), Function.Injective inc ∧ LinearMap.range inc = Submodule.span ℂ {y | ∃ i P, y = j i P} ∧ ∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y) := by
  first | exact @GlobalTheory.ArchRec.SpanMod.exists_unitary_span | exact GlobalTheory.ArchRec.SpanMod.exists_unitary_span | (intros; apply GlobalTheory.ArchRec.SpanMod.exists_unitary_span <;> assumption)
