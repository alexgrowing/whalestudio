import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ThetaFirstVar

open GlobalTheory.Size

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    ∀ γ ∈ GQ V, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D V × GA D W) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    Continuous fun g => thetaKO ω g h f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_left h)

theorem thetaKO_modGrowth_fst (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    (h : GA D W) : GlobalTheory.Grow.ModGrowth V fun g => thetaKO ω g h f := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * GlobalTheory.Grow.height W h ^ A, A, fun g => ?_⟩
  rw [mul_assoc _ (GlobalTheory.Grow.height W h ^ A), ← mul_pow, mul_comm (GlobalTheory.Grow.height W h)]
  exact (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h

theorem thetaKO_mul_conj_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  intro hP D ψ S T χS χT om hω θ hθ ν 𝓕 hν h𝓕 u y hu hy hc a x
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S fun g => conj (y (g * a)) :=
    ((GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).mul_right a).conj
  exact hR.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth_fst hθ hω hu x) (thetaKO_left_fst hω hu x)
    (thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

end GlobalTheory.ChainOnto.ThetaFirstVar

end
