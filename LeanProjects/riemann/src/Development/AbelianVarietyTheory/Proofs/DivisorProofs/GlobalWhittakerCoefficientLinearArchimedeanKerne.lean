import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.WhitAlg

open GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_psiNeg :
    Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem whit_eq (F : GA E a → ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit F g = ∫ X in vecDomain E (Pos a),
      F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := rfl

theorem integrableOn_whit {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) :
    IntegrableOn (fun X => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hF.comp (continuous_uGL.mul continuous_const)).mul continuous_psiNeg
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add_mul {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (c : ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g := by
  rw [whit_eq, whit_eq, whit_eq, ← integral_const_mul,
    ← integral_add (integrableOn_whit hF g) ((integrableOn_whit hG g).const_mul c)]
  congr 1
  funext X
  ring

theorem whit_kerInf {F : GA E a → ℂ} (hF : Continuous F)
    (hgr : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N)
    {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : GlobalTheory.JSW.IsRapidInf ν k γ) (g : GA E a) :
    GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  let ψ : (Pos a → Ad E) → ℂ := fun Y => (GroundTheory.Global.adelicChar E (-supSum 0 Y) : ℂ)
  let f : (Pos a → Ad E) → X → ℂ := fun Y x => k x * F (uGL Y * g * infGL E a (γ x)) * ψ Y
  have hmeas : Measurable (Function.uncurry f) := by
    haveI : BorelSpace ((Pos a → Ad E) × Lie E a) := Prod.borelSpace
    have hc : ContinuousOn (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) :=
      (GlobalTheory.ConstTermSmooth.continuousOn_chart hF).comp
        (((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hφ : Measurable fun p : (Pos a → Ad E) × X => ((p.1, toL (γ p.2).val) : (Pos a → Ad E) × Lie E a) :=
      measurable_fst.prodMk (hk.2.1.comp measurable_snd)
    have h1 : Measurable fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val) := by
      have e : (fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val)) =
          (Set.univ ×ˢ invSet E a).restrict (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2) ∘
            fun p => (⟨(p.1, toL (γ p.2).val), Set.mem_univ _, val_mem_invSet _⟩ :
              (Set.univ ×ˢ invSet E a : Set ((Pos a → Ad E) × Lie E a))) := rfl
      rw [e]
      exact hc.restrict.measurable.comp hφ.subtype_mk
    have e2 : Function.uncurry f = fun p => k p.2 * chart F (uGL p.1 * g) (toL (γ p.2).val) * ψ p.1 := by
      funext p
      exact congrArg (fun z => k p.2 * z * ψ p.1) (chart_val F _ _).symm
    rw [e2]
    exact ((hk.1.comp measurable_snd).mul h1).mul (continuous_psiNeg.measurable.comp measurable_fst)
  obtain ⟨C, N, hC⟩ := hgr ((fun Y => uGL Y * g) '' closure (vecDomain E (Pos a)))
    (isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const))
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hb : Integrable (fun p : (Pos a → Ad E) × X => (1 : ℝ) * (C * (‖k p.2‖ * height (γ p.2) ^ N))) (μ.prod ν) :=
      (integrable_const (1 : ℝ)).mul_prod ((hk.2.2 N).const_mul C)
    have hae : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ vecDomain E (Pos a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_vecDomain)
    refine hb.mono' hmeas.aestronglyMeasurable (hae.mono fun p hp => ?_)
    have hb1 := hC (uGL p.1 * g) ⟨p.1, subset_closure hp, rfl⟩ (γ p.2)
    change ‖k p.2 * F (uGL p.1 * g * infGL E a (γ p.2)) * (GroundTheory.Global.adelicChar E (-supSum 0 p.1) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    calc ‖k p.2‖ * ‖F (uGL p.1 * g * infGL E a (γ p.2))‖ ≤ ‖k p.2‖ * (C * height (γ p.2) ^ N) :=
          mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
      _ = 1 * (C * (‖k p.2‖ * height (γ p.2) ^ N)) := by ring
  have hin : ∀ Y, GlobalTheory.JSW.kerInf ν k γ F (uGL Y * g) * ψ Y = ∫ x, f Y x ∂ν := fun Y => by
    simp only [f, GlobalTheory.JSW.kerInf]
    rw [integral_mul_const]
  calc GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ Y, ∫ x, f Y x ∂ν ∂μ := by
        rw [whit_eq]
        congr 1
        funext Y
        exact hin Y
    _ = ∫ x, ∫ Y, f Y x ∂μ ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext x
        rw [whit_eq, ← integral_const_mul]
        congr 1
        funext Y
        simp only [f, ψ, mul_assoc]

theorem whit_linear_kerInf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ),
    Continuous F → Continuous G →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧
      ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
        GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g =
          ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  intro E _ _ _ a F G hF hG hFg _
  exact ⟨fun c g => whit_add_mul hF hG c g, fun X _ ν _ k γ hk g => whit_kerInf hF hFg ν hk g⟩

end GlobalTheory.JSW.WhitAlg
