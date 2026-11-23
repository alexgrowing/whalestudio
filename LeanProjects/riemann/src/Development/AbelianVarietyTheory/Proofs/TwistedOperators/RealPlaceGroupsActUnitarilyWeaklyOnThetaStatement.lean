import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
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
theorem _root_.GlobalTheory.T.realPlaceGroups_act_unitarily_weakly_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  first | exact @GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | exact GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | (intros; apply GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain <;> assumption)
