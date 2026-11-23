import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomialStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerY

theorem hasDerivAt_thetaSum_lineY : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ f f₁ r hR hD u
  by_cases hf : f = 0
  ·
    subst hf
    have hR0 : Rest (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r := hR
    have ht0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by
      funext x; simp [tens]
    have h1 : tens (evI F) (⇑f₁) r = 0 := by
      funext x
      have h := hD r hR0 x
      simp only [ht0, map_zero] at h
      exact (h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))).trans rfl
    have hrho0 : M.co.rho ψ u 0 = 0 := by
      funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hth0 : GlobalTheory.WeilM.thetaSum F (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
      simp [GlobalTheory.WeilM.thetaSum]
    simp only [ht0, h1, map_zero, hrho0, hth0]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  obtain ⟨c, g, hc, hlim⟩ := GlobalTheory.T.weil_line_good_model_polynomial hP M ψ χX χW om hψ hG hW γ hγ f r hR
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum M ψ hψ u f r hR hf
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r))))
      = fun t => Λ (c t) := by
    funext t
    rw [hc t]
    exact (hΛ (c t)).tsum_eq
  have ev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      Continuous fun s : SInf F (Fin n × Fin d) => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have hg : tens (evI F) (⇑g) r = tens (evI F) (⇑f₁) r := by
    funext x
    have h1 := hD r hR x
    have h2 : HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) (tens (evI F) (⇑g) r x) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, tens]
      rw [slope_def_module]
      simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    have h3 : (fun t : ℝ => tens (evI F) (⇑(c t)) r x) =
        fun t => om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) (⇑f) r) x := by
      funext t; rw [hc t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (tens (evI F) (⇑f₁) r)) = Λ g := by
    rw [← hg]; exact (hΛ g).tsum_eq
  rw [hcurve, hend, hasDerivAt_iff_tendsto_slope]
  refine (Λ.continuous.tendsto g |>.comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp [slope_def_module, map_sub, map_smul]

end GlobalTheory.ThetaLineDerY
