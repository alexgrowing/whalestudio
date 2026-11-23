import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftGrowthDef

theorem lift_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'

end GlobalTheory.LiftGrowthDef
