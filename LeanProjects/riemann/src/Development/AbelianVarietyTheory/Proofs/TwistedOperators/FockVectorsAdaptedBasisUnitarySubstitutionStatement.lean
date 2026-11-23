import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAdaptedBasisUnitarySubstitution
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
theorem _root_.GlobalTheory.T.fockVectors_adaptedBasis_unitary_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ BS BT, IsAdapted (gramAt D S τ) sS BS → IsAdapted (gramAt D T τ) sT BT → ∃ ς : LPol T.rank S.rank ≃ₗ[ℂ] LPol T.rank S.rank, Graded ς ∧ (∀ P Q, fockIp (ς P) (ς Q) = fockIp P Q) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ P, ptAt ψ θ S T τ sS sT BS BT f P = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (ς P) := by
  first | exact @GlobalTheory.ArchRec.BasisChange.ptAt_basis | exact GlobalTheory.ArchRec.BasisChange.ptAt_basis | (intros; apply GlobalTheory.ArchRec.BasisChange.ptAt_basis <;> assumption)
