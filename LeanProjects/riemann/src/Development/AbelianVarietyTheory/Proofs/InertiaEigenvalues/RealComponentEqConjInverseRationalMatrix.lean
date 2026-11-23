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

namespace GlobalTheory.ArchRatComp

theorem compAt_mt_eq_map_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E),
    γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → ∀ τ : D.what₂.Tau, ∃ σ : D.host.E →+* ℂ,
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map σ := by
  intro D θ _ V γ a γ' _ hrat _ hfc τ
  refine ⟨(θ τ).comp ((infPart D).comp (incA D)), ?_⟩
  have h1 : infHom V (γ * a) = 1 := hfc
  have h2 : infHom V a = (infHom V γ)⁻¹ := by
    rw [map_mul] at h1; exact eq_inv_of_mul_eq_one_right h1
  have h3 : infHom V γ = Formalism.UG.bc ((infPart D).comp (incA D)) γ' := by
    show (Formalism.UG.bc _) (matHom V γ) = _
    rw [hrat]
    ext i j
    rfl
  have h4 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((infHom V a).val).map (θ τ) := rfl
  rw [h4, h2, h3, ← map_inv]
  ext i j
  rfl

end GlobalTheory.ArchRatComp
