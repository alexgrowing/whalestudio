import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RightRegExists

open GlobalTheory.RightRegFund

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G} {r : G → G}

theorem eLpNorm_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (f : G → ℂ) (g : G) :
    eLpNorm (fun x => f (r (x * g))) 2 (μ.restrict D) = eLpNorm f 2 (μ.restrict D) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    lintegral_comp_rep_mul hD hDm hr (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal) g]

theorem memLp_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (F : Lp ℂ 2 (μ.restrict D)) (g : G) :
    MemLp (fun x => (F : G → ℂ) (r (x * g))) 2 (μ.restrict D) := by
  refine ⟨?_, ?_⟩
  · exact ((aestronglyMeasurable_comp_rep hD hDm hr
      (Lp.stronglyMeasurable F)).comp_quasiMeasurePreserving
        (measurePreserving_mul_right μ g).quasiMeasurePreserving).restrict
  · rw [eLpNorm_comp_rep_mul hD hDm hr]
    exact Lp.eLpNorm_lt_top F

theorem ae_rep_mul (hDm : MeasurableSet D) (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    {p : G → Prop} (hp : ∀ᵐ x ∂(μ.restrict D), p x) (g : G) :
    ∀ᵐ x ∂(μ.restrict D), p (r (x * g)) :=
  ae_restrict_of_ae
    ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae (ae_rep hDm hr hp))

theorem exists_rightTranslation (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (g : G) :
    ∃ T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D),
      ∀ F, (T F : G → ℂ) =ᵐ[μ.restrict D] fun x => (F : G → ℂ) (r (x * g)) := by
  let T₀ : Lp ℂ 2 (μ.restrict D) → Lp ℂ 2 (μ.restrict D) := fun F =>
    (memLp_comp_rep_mul hD hDm hr F g).toLp _
  have hT : ∀ F, (T₀ F : G → ℂ) =ᵐ[μ.restrict D] fun x => (F : G → ℂ) (r (x * g)) :=
    fun F => MemLp.coeFn_toLp _
  let T₁ : Lp ℂ 2 (μ.restrict D) →ₗ[ℂ] Lp ℂ 2 (μ.restrict D) :=
    { toFun := T₀
      map_add' := fun F F' => Lp.ext <| by
        filter_upwards [hT (F + F'), hT F, hT F', Lp.coeFn_add (T₀ F) (T₀ F'),
          ae_rep_mul hDm hr (Lp.coeFn_add F F') g] with x h1 h2 h3 h4 h5
        rw [h1, h4, h5, Pi.add_apply, Pi.add_apply, h2, h3]
      map_smul' := fun c F => Lp.ext <| by
        filter_upwards [hT (c • F), hT F, Lp.coeFn_smul c (T₀ F),
          ae_rep_mul hDm hr (Lp.coeFn_smul c F) g] with x h1 h2 h4 h5
        rw [RingHom.id_apply, h1, h4, h5, Pi.smul_apply, Pi.smul_apply, h2] }
  refine ⟨T₁.mkContinuous 1 fun F => ?_, hT⟩
  change ‖T₀ F‖ ≤ _
  rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hT F), eLpNorm_comp_rep_mul hD hDm hr]

end Abstract

theorem exists_rightReg : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∃ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R ∧ R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  intro I μf _ _ fund hfund
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.RatDiscrete.rational_points I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  choose R hR using exists_rightTranslation hD hfund.1 hr
  exact ⟨R, hR, RightRegFund.map_one hD hfund.1 hr hR, RightRegFund.map_mul hD hfund.1 hr hR,
    norm_map hD hfund.1 hr hR, continuous_map hD hfund.1 hr hR⟩

end GlobalTheory.RightRegExists
