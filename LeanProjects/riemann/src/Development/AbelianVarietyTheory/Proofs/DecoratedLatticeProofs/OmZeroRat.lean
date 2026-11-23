import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSumProof

variable {D : D7}

theorem om_zero_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ hf)

theorem liftSum : ∀ D : D7, LiftSum D := by
  intro D ψ θ hθ S T x y hx hy k hk P
  obtain ⟨χS, χT, hω⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hk.vac.1
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hcomb : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 k.vac hvac (WO S T) k.c.support id k.c (fun u hu => hk.fin u hu)
  have hpt : IsThetaFunO ψ S T (k.pt ψ θ x y P) :=
    GlobalTheory.FockTheta.ptStable D ψ θ hψ hθ S T x.s y.s x.B y.B _ P hcomb

  have key : ∀ φ : GA D S → ℂ, IsContAut S φ →
      (∀ h, IntegrableOn (fun g => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) x.vol.𝓕 x.vol.μ) ∧
      Continuous fun h => ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ := by
    intro φ hφ
    have hc : Continuous (Function.uncurry fun (g : GA D S) (h : GA D T) => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) :=
      (hω.om_cont _ hpt 0).mul (hφ.2.comp continuous_fst)
    have hinv : ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T),
        k.om (γ * g, h) (k.pt ψ θ x y P) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y P) 0 * φ g := by
      intro γ hγ g h
      have e := om_zero_rat hω hpt hγ (one_mem (GQ T)) g h
      rw [one_mul] at e
      rw [e, hφ.1 γ hγ g]
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hx.cpt x.vol (GA D T) _ hc hinv
    exact ⟨h1, h2⟩
  refine ⟨hpt, fun φ hφ => ⟨fun γ' hγ' h => ?_, ?_⟩, fun I s a φ hφ => ?_⟩
  · show ∫ g in x.vol.𝓕, k.om (g, γ' * h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ =
      ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ
    congr 1
    funext g
    have e := om_zero_rat hω hpt (one_mem (GQ S)) hγ' g h
    rw [one_mul] at e
    rw [e]
  · exact (key φ hφ).2
  · funext h
    show ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * (∑ i ∈ s, a i • φ i) g ∂x.vol.μ =
      (∑ i ∈ s, a i • fun h' => ∫ g in x.vol.𝓕, k.om (g, h') (k.pt ψ θ x y P) 0 * φ i g ∂x.vol.μ) h
    rw [Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : (fun g => ∑ i ∈ s, k.om (g, h) (k.pt ψ θ x y P) 0 * (a i * φ i g)) =
        fun g => ∑ i ∈ s, a i * (k.om (g, h) (k.pt ψ θ x y P) 0 * φ i g) := by
      funext g
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finset_sum s (fun i hi => ((key (φ i) (hφ i hi)).1 h).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul (a i) _

end GlobalTheory.SeeSaw.LiftSumProof

end
