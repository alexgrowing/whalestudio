import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowthStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.LiftRapid

theorem lift_conv_cont_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (v : Vol T) (G : GA D T → ℂ) (f : WO S T → ℂ), RapidDec T G → IsThetaFunO ψ S T f → (∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ) ∧ IsAutFun S (liftS om v.μ v.𝓕 G f) ∧ IsContAut S (liftS om v.μ v.𝓕 G f) ∧ ModGrowth S (liftS om v.μ v.𝓕 G f) ∧ ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) := by
  intro D ψ S T χS χT om hω v G f hG hf
  have hν := v.haar
  have h𝓕 := v.fund
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : SecondCountableTopology (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.1
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν h𝓕)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilOperator_thetaFun_sup_moderate_growth D ψ S T χS χT om hω f hf
  obtain ⟨B, hB⟩ := hG.decay A
  have hk : ∀ g h, ‖om (g, h) f 0‖ ≤ C * height S g ^ A * height T h ^ A := fun g h => by
    rw [mul_assoc, ← mul_pow]; exact hC g h 0
  have hleft := fun g => GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g
  have hcont := fun g => GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf g
  have hint : ∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ := fun g =>
    hG.integrableOn_modGrowth_mul hν h𝓕 ⟨C * height S g ^ A, A, hk g⟩ (hleft g)
      (hcont g).measurable.aestronglyMeasurable
  have hbd : ∀ g h, ‖om (g, h) f 0 * G h‖ ≤ C * 2 ^ A * B * height S g ^ A := fun g h => by
    have h1 := norm_le_quotHeight_pow (f := fun h => thetaKO om g h f) (hleft g) (hk g) h
    have hC0 : 0 ≤ C * height S g ^ A * 2 ^ A :=
      (mul_nonneg (nonneg_of_growth (hk g)) (by positivity))
    rw [norm_mul]
    calc ‖om (g, h) f 0‖ * ‖G h‖ ≤ C * height S g ^ A * 2 ^ A * quotHeight T h ^ A * ‖G h‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * height S g ^ A * 2 ^ A * (‖G h‖ * quotHeight T h ^ A) := by ring
      _ ≤ C * height S g ^ A * 2 ^ A * B := mul_le_mul_of_nonneg_left (hB h) hC0
      _ = C * 2 ^ A * B * height S g ^ A := by ring
  have hm : ∀ g, AEStronglyMeasurable (fun h => om (g, h) f 0 * G h) (v.μ.restrict v.𝓕) := fun g =>
    ((hcont g).mul hG.continuous).measurable.aestronglyMeasurable
  have hc : Continuous (liftS om v.μ v.𝓕 G f) := by
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    have hcb : Continuous fun g => C * 2 ^ A * B * height S g ^ A := continuous_const.mul ((continuous_height S).pow A)
    have hev := hcb.continuousAt.eventually_lt (continuousAt_const (y := C * 2 ^ A * B * height S g₀ ^ A + 1))
      (lt_add_one _)
    exact continuousAt_of_dominated (bound := fun _ => C * 2 ^ A * B * height S g₀ ^ A + 1)
      (.of_forall hm) (hev.mono fun g hg => .of_forall fun h => (hbd g h).trans hg.le) (integrable_const _)
      (.of_forall fun h => (((hω.om_cont f hf 0).comp (Continuous.prodMk_left h)).mul continuous_const).continuousAt)
  have hl : ∀ γ ∈ GQ S, ∀ g, liftS om v.μ v.𝓕 G f (γ * g) = liftS om v.μ v.𝓕 G f g := fun γ hγ g => by
    have e : ∀ h, om (γ * g, h) f 0 = om (g, h) f 0 := fun h => by
      have e' : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
      rw [e', map_mul, Module.End.mul_apply]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)
    simp only [liftS_apply, e]
  have heq : ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) :=
    fun g₀ h₀ => GlobalTheory.Chain.LiftReg.lift_om hω hν h𝓕 hf hG.1 g₀ h₀
  refine ⟨hint, ⟨hl, ?_, hc⟩, ⟨hl, hc⟩, ⟨C * 2 ^ A * B * (v.μ.restrict v.𝓕).real Set.univ, A, fun g => ?_⟩, heq⟩
  · obtain ⟨U, U', hU, -, e⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hω.std S T om (GlobalTheory.Ker.isWeak_of_datum hω)
      hω.om_cont f hf
    refine ⟨U, hU, fun k h1 h2 g => ?_⟩
    have := congrFun (heq k 1) g
    rw [e k h1 h2 1 (one_mem _) (one_mem _), show rTrans 1 G = G from funext fun h => congrArg G (mul_one h)] at this
    exact this.symm
  · rw [liftS_apply]
    refine (norm_integral_le_of_norm_le_const (.of_forall fun h => hbd g h)).trans_eq ?_
    ring

end GlobalTheory.Unf.LiftRapid

end
