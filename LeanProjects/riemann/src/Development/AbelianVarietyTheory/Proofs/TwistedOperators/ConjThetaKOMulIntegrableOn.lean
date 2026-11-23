import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowConv

theorem thetaKO_toSgn {D : D7} {S T : HSp D} (om : GlobalTheory.Grid.WRep S T) (h : GA D S) (g : GA D T) (f : WO S T → ℂ) :
    thetaKO om h g f = thetaKO (om.toSgn true) ((GlobalTheory.Grid.ofSgn true S).symm h) g f := by
  unfold thetaKO GlobalTheory.Grid.WRep.toSgn
  simp

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    ∀ γ ∈ GQ T, ∀ g, thetaKO om h (γ * g) f = thetaKO om h g f := fun γ hγ g => by
  have e : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) _ hγ _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    Continuous fun g => thetaKO om h g f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_right h)

theorem conj_thetaKO_modGrowth_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    GlobalTheory.Grow.ModGrowth T fun g => conj (thetaKO om h g f) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ S T χS χT om hω f hf
  refine ⟨C * GlobalTheory.Grow.height S h ^ A, A, fun g => ?_⟩
  rw [RCLike.norm_conj, mul_assoc, ← mul_pow]
  exact hC h g

theorem conj_thetaKO_mul_integrableOn (hP : GlobalTheory.Published.CuspRapidDecay)
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Ainf ↥D.host.F) D.host.E →+* ℂ} (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ)
    (hc : IsCuspFun T φ) (h : GA D S) :
    IntegrableOn (fun g => conj (thetaKO om h g f) * φ g) 𝓕 ν :=
  (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc).integrableOn_modGrowth_mul hν h𝓕
    (conj_thetaKO_modGrowth_snd hω hf h)
    (fun γ hγ g => by simp only [thetaKO_left_snd hω hf h γ hγ g])
    ((Complex.continuous_conj.comp (thetaKO_continuous_snd hω hf h)).measurable.aestronglyMeasurable)

end GlobalTheory.UpArrowConv
