import Mathlib

noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open MeasureTheory Filter Topology

def BC {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

section

variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}

theorem BC.mul (h : BC f) (h' : BC g) : BC fun x => f x * g x := by
  obtain ⟨a, C, hC⟩ := h
  obtain ⟨b, C', hC'⟩ := h'
  exact ⟨a.mul b, C * C', fun x => (norm_mul_le _ _).trans
    (mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))⟩

theorem BC.star (h : BC f) : BC fun x => star (f x) := ⟨h.1.star, h.2.imp fun _ h x => (norm_star _).trans_le (h x)⟩

theorem BC.comp (h : BC f) {u : X' → X} (hu : Continuous u) : BC fun x => f (u x) := ⟨h.1.comp hu, h.2.imp fun _ h _ => h _⟩

theorem BC.int [MeasurableSpace X] [OpensMeasurableSpace X] (h : BC f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound h.1.aestronglyMeasurable _ (.of_forall h.2.choose_spec)

end

variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}

theorem at_value {θ : H × G → ℂ} (hθ : BC θ) (hφ : BC φ) :
    ∫ y, (∫ g, θ (g, y.1) * star (θ (g, y.2)) ∂ρ) * (φ y.2 * star (φ y.1)) ∂ν.prod ν =
      ∫ g, (∫ h, φ h * star (θ (g, h)) ∂ν) * star (∫ h, φ h * star (θ (g, h)) ∂ν) ∂ρ := by
  simp only [← integral_mul_const]
  rw [integral_integral_swap (f := fun (y : G × G) g => θ (g, y.1) * star (θ (g, y.2)) * (φ y.2 * star (φ y.1)))
    (BC.int (((hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.1)) (by fun_prop)).mul
      (hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.2)) (by fun_prop)).star).mul
      ((hφ.comp (by fun_prop)).mul (hφ.comp (by fun_prop)).star)) _)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only [integral_mul_const]
  rw [mul_comm, Complex.star_def, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

theorem far_right [Group G] [ContinuousMul G] (μ : Measure G) [SFinite μ] {k : G × G → ℂ} {w : G → ℂ} (hk : BC k) (hφ : BC φ)
    (hw : Integrable w μ) (h : ∀ h, ∫ h', k (h, h') * φ h' ∂ν = ∫ g, w g * φ (h * g) ∂μ) :
    ∫ y, k y * (φ y.2 * star (φ y.1)) ∂ν.prod ν = ∫ g, w g * ∫ h, φ (h * g) * star (φ h) ∂ν ∂μ := by
  rw [integral_prod _ (BC.int (hk.mul ((hφ.comp continuous_snd).mul (hφ.comp continuous_fst).star)) _)]
  simp only [← mul_assoc, integral_mul_const, h]
  simp only [← integral_mul_const, ← integral_const_mul, mul_assoc]
  obtain ⟨c, C, hC⟩ := (hφ.comp (u := fun y : G × G => y.1 * y.2) (by fun_prop)).mul (hφ.comp continuous_fst).star
  exact integral_integral_swap (f := fun h g => w g * (φ (h * g) * star (φ h)))
    ((hw.comp_snd ν).mul_bdd c.aestronglyMeasurable (.of_forall hC))

theorem ident {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {g g' : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg' : DifferentiableOn ℂ g' U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ g s = g' s) {s : ℂ} (hs : s ∈ U) : g s = g' s := by
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg'.analyticOnNhd hU) hc (h _ h1).1 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (h z hz).2

end GlobalTheory.ThK.Dbl.An

end
