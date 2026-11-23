import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_conj {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) :
    Integrable (fun x => f x * conj (h x)) μ := by
  have cf : Continuous f := hf.1.continuous
  have ch : Continuous h := hh.1.continuous
  exact (cf.mul (Complex.continuous_conj.comp ch)).integrable_of_hasCompactSupport
    (hf.2.mul_right)

theorem conj_mem {h : X → ℂ} (hh : h ∈ SB X) : (fun y => conj (h y)) ∈ SB X :=
  ⟨hh.1.comp _, hh.2.comp_left (map_zero _)⟩

theorem self_eq {g : X → ℂ} (hg : g ∈ SB X) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∧
    (∫ x, g x * conj (g x) ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi : Integrable (fun x => g x * conj (g x)) μ := integrable_mul_conj μ hg hg
  have hn : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    have := hi.norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · rw [ofReal_integral_eq_lintegral_ofReal hn (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  · rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem expand {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) (c : ℂ) :
    ∫ x, (c • h + f) x * conj ((c • h + f) x) ∂μ =
      c * conj c * ∫ x, h x * conj (h x) ∂μ + c * ∫ x, h x * conj (f x) ∂μ +
      conj c * ∫ x, f x * conj (h x) ∂μ + ∫ x, f x * conj (f x) ∂μ := by
  have e : (fun x => (c • h + f) x * conj ((c • h + f) x)) =
      fun x => (c * conj c) * (h x * conj (h x)) + c * (h x * conj (f x)) +
        conj c * (f x * conj (h x)) + f x * conj (f x) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact integrable_mul_conj μ hf hf
    | exact (integrable_mul_conj μ hh hh).const_mul _
    | exact (integrable_mul_conj μ hh hf).const_mul _
    | exact (integrable_mul_conj μ hf hh).const_mul _
    | exact ((integrable_mul_conj μ hh hh).const_mul _).add ((integrable_mul_conj μ hh hf).const_mul _)
    | exact (((integrable_mul_conj μ hh hh).const_mul _).add
        ((integrable_mul_conj μ hh hf).const_mul _)).add ((integrable_mul_conj μ hf hh).const_mul _)

end GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate in

theorem GlobalTheory.PolarSB.pairing_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  intro F _ _ κ _ v T hSB hlin μ hμ hnorm φ₁ h₁ φ₂ h₂
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  set w : (κ → Fv F v) → ℂ := fun y => starRingEnd ℂ (φ₂ y) with hw
  have hwSB : w ∈ SB (κ → Fv F v) := GlobalTheory.PolarSB.conj_mem h₂
  have hN : ∀ g ∈ SB (κ → Fv F v),
      ∫ x, T g x * conj (T g x) ∂μ = ∫ x, g x * conj (g x) ∂μ := by
    intro g hg
    obtain ⟨a1, a2⟩ := GlobalTheory.PolarSB.self_eq μ hg
    obtain ⟨b1, b2⟩ := GlobalTheory.PolarSB.self_eq μ (hSB g hg)
    rw [a2, b2]
    congr 1
    have := hnorm g hg
    rw [← a1, ← b1] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)).1 this
  have key : ∀ c : ℂ,
      c * ∫ x, T w x * conj (T φ₁ x) ∂μ + conj c * ∫ x, T φ₁ x * conj (T w x) ∂μ =
      c * ∫ x, w x * conj (φ₁ x) ∂μ + conj c * ∫ x, φ₁ x * conj (w x) ∂μ := by
    intro c
    have hm : c • w + φ₁ ∈ SB (κ → Fv F v) := add_mem (Submodule.smul_mem _ c hwSB) h₁
    have e1 := hN _ hm
    rw [hlin w hwSB φ₁ h₁ c, GlobalTheory.PolarSB.expand μ h₁ hwSB c,
      GlobalTheory.PolarSB.expand μ (hSB _ h₁) (hSB _ hwSB) c, hN _ h₁, hN _ hwSB] at e1
    linear_combination e1
  have k1 := key 1
  have kI := key Complex.I
  simp only [map_one, one_mul, Complex.conj_I] at k1 kI
  have hfin : ∫ x, T φ₁ x * conj (T w x) ∂μ = ∫ x, φ₁ x * conj (w x) ∂μ := by
    linear_combination (k1 + Complex.I * kI) / 2 +
      (-(∫ x, T w x * conj (T φ₁ x) ∂μ) + ∫ x, T φ₁ x * conj (T w x) ∂μ
        + ∫ x, w x * conj (φ₁ x) ∂μ - ∫ x, φ₁ x * conj (w x) ∂μ) / 2 * Complex.I_sq
  rw [hfin]
  simp [hw]
