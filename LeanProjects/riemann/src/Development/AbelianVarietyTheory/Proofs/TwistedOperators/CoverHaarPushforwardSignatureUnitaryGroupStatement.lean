import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverHaarPushforwardSignatureUnitaryGroup
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
theorem _root_.GlobalTheory.T.cover_haar_pushforward_signatureUnitaryGroup : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  first | exact @GlobalTheory.ArchRec.cover_haar_map | exact GlobalTheory.ArchRec.cover_haar_map | (intros; apply GlobalTheory.ArchRec.cover_haar_map <;> assumption)
