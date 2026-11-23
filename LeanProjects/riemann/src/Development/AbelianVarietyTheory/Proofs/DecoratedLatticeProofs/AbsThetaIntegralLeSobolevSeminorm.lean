import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolevStatement
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem tendsto_enorm_of_le {v : ℕ → ℂ} {a : ℂ} {s : ℕ → ℝ≥0∞} (C : ℝ≥0) (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (h : ∀ j, ‖v j - a‖ₑ ≤ C * s j) : Filter.Tendsto (fun j => ‖v j‖ₑ) Filter.atTop (nhds ‖a‖ₑ) := by
  have h1 : Filter.Tendsto (fun j => (C : ℝ≥0∞) * s j) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hs (Or.inr ENNReal.coe_ne_top)
  have h2 : Filter.Tendsto (fun j => edist (v j) a) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      (fun j => by simpa [edist_eq_enorm_sub] using h j)
  exact (continuous_enorm.tendsto a).comp (tendsto_iff_edist_tendsto_0.2 h2)

theorem sobBdd_absThetaInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ Z : (WO S T → ℂ) → WO S T → ℂ, (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Z (f + f') = Z f + Z f') → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Z (c • f) = c • Z f) → Sobolev₂ ψ θ μ 𝓕 μ 𝓕 Z → (∀ f, IsThetaFunO ψ S T f → ∀ x, om (x, 1) (Z f) = Z (om (x, 1) f)) → (∀ f, IsThetaFunO ψ S T f → Integrable (descend (GQ T) fun h => thetaKO om 1 h (Z f)) (autMeasure T m)) → SobBdd ψ θ μ 𝓕 fun f x => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om x h (Z f)) q‖ₑ ∂autMeasure T m := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hc m _ Z hadd hsm hZ hcomm hint U hU K hK
  obtain ⟨U', hU', hl, hb⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc (K ×ˢ {1})
    (hK.prod isCompact_singleton) U hU
  have pt : ∀ h : GA D T, ∃ (d : ℕ) (C : ℝ≥0), ∀ g ∈ thetaLevel ψ S T U',
      ‖thetaKO om 1 h (Z g)‖ₑ ≤ C * sobO ψ θ μ 𝓕 d g := by
    intro h
    obtain ⟨U₁, hU₁, hl₁, hb₁⟩ := hZ U' hU'
    obtain ⟨U₂, hU₂, hl₂, hb₂⟩ := GlobalTheory.T.exists_common_level_sobolev_bound_weil_compact D ψ S T χS χT om hom θ hθ μ 𝓕 hc {(1, h)}
      isCompact_singleton U₁ hU₁
    obtain ⟨d₃, C₃, hb₃⟩ := GlobalTheory.T.exists_sobolev_bound_theta_pointwise D ψ hom.std θ hθ S T μ 𝓕 hc U₂ hU₂
    obtain ⟨d₂, C₂, hb₂⟩ := hb₂ d₃
    obtain ⟨d₁, C₁, hb₁⟩ := hb₁ d₂
    refine ⟨d₁, C₃ * (C₂ * C₁), fun g hg => ?_⟩
    refine (hb₃ _ (hl₂ _ (hl₁ g hg) _ rfl) 0).trans ?_
    rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc, mul_assoc]
    gcongr
    refine (hb₂ _ (hl₁ g hg) _ rfl).trans ?_
    gcongr
    exact hb₁ g hg
  obtain ⟨d, C, hN⟩ := GlobalTheory.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev D ψ hom.std θ hθ S T μ 𝓕 hc U' hU'
    (fun f => ∫⁻ q, ‖descend (GQ T) (fun h => thetaKO om 1 h (Z f)) q‖ₑ ∂autMeasure T m)
    (fun f hf g hg => by
      rw [← lintegral_add_left' (hint f hf.1).1.enorm]
      refine lintegral_mono fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hadd f g hf.1 hg.1, map_add, Pi.add_apply]
      exact enorm_add_le _ _)
    (fun c f hf => by
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun q => ?_
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, hsm c f hf.1, map_smul, Pi.smul_apply, enorm_smul])
    (fun f hf => (hint f hf.1).2.ne)
    (fun u hu f hf ht => by
      refine le_trans (lintegral_mono fun q => ?_) (lintegral_liminf_le' fun j => (hint _ (hu j).1).1.enorm)
      obtain ⟨d, C, hp⟩ := pt (Quotient.out q)
      refine (tendsto_enorm_of_le C (ht d) fun j => ?_).liminf_eq.ge
      refine le_of_eq_of_le ?_ (hp _ (sub_mem (hu j) hf))
      have e : u j - f = u j + (-1 : ℂ) • f := by rw [neg_one_smul, sub_eq_add_neg]
      have hf' : (-1 : ℂ) • f ∈ thetaLevel ψ S T U' := Submodule.smul_mem _ _ hf
      rw [e, hadd _ _ (hu j).1 hf'.1, hsm _ _ hf.1]
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, neg_one_smul,
        sub_eq_add_neg, map_neg, Pi.neg_apply])
  obtain ⟨d', C', hb⟩ := hb d
  refine ⟨d', C * C', fun f hf x hx => ?_⟩
  have hx' : ((x, 1) : GA D S × GA D T) ∈ K ×ˢ {1} := ⟨hx, rfl⟩
  refine le_of_eq_of_le ?_ ((hN _ (hl f hf _ hx')).trans ?_)
  · refine lintegral_congr fun q => ?_
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
    rw [← hcomm f hf.1 x, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  · rw [ENNReal.coe_mul, mul_assoc]
    gcongr
    exact hb f hf _ hx'

end GlobalTheory.ThetaDens
