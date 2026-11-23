import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.FourierLocInv

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem inversion_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → k), ∀ a : κ → k,
      ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ = d * φ (-a) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨((r : ℝ) : ℂ) ^ 2, pow_ne_zero 2 hr', fun φ hφ a => ?_⟩
  have hg : (fun x => φ (x + -a)) ∈ SB (κ → k) :=
    ⟨hφ.1.comp_continuous (Homeomorph.addRight (-a)).continuous, hφ.2.comp_homeomorph (Homeomorph.addRight (-a))⟩
  have key := (GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν _ hg).2
  have hinner : ∀ y, ∫ x, φ (x + -a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m
      = (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) := by
    intro y
    rw [GlobalTheory.FourierLocBij.translate_fourier, neg_dotProduct, neg_neg, dotProduct_comm a y, mul_comm]
  have key' : ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) ∂m = φ (-a) := by
    refine Eq.trans ?_ (key.trans (congrArg φ (zero_add (-a))))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hinner y).symm
  have hsm : ∀ G : (κ → k) → ℂ, ∫ y, G y ∂μ = ((r : ℝ) : ℂ) * ∫ y, G y ∂m := by
    intro G
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hfun : (fun y => (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ)) =
      fun y => ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) := by
    funext y
    rw [hsm, mul_assoc]
  rw [show (∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ) =
      ∫ y, ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) ∂μ from congrArg _ hfun,
    integral_const_mul, hsm, key']
  ring

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  intro F _ _ v χ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (GlobalTheory.FourierLocBij.toCircle χ hn) := Continuous.subtype_mk hc _
  have hne : GlobalTheory.FourierLocBij.toCircle χ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [GlobalTheory.FourierLocBij.coe_toCircle] using
      congrArg (fun ψ : AddChar (Fv F v) Circle => ((ψ t : Circle) : ℂ)) h
  exact inversion_circle (GlobalTheory.FourierLocBij.toCircle χ hn) hcont hne κ μ

end GlobalTheory.FourierLocInv
