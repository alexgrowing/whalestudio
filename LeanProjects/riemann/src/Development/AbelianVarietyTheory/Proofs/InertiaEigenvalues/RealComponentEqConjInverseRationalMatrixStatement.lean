import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealComponentEqConjInverseRationalMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realComponent_eq_conj_inverse_rationalMatrix : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E),
    γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → ∀ τ : D.what₂.Tau, ∃ σ : D.host.E →+* ℂ,
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map σ := by
  first | exact @GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv | exact GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv | (intros; apply GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv <;> assumption)
