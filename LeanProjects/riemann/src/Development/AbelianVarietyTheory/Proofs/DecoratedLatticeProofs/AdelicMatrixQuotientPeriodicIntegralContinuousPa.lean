import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.ParCont

variable {D : D7} {m n : ℕ}

theorem eventually_close {P : Type} [TopologicalSpace P] (K : Mx D m n → P → ℂ) (hc : Continuous (Function.uncurry K))
    (hp : ∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ x, ‖K x p - K x p₀‖ ≤ ε := by
  obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
  have h : ∀ᶠ p in nhds p₀, ∀ x ∈ C, ‖K x p - K x p₀‖ < ε := by
    refine hC.eventually_forall_of_forall_eventually (P := fun p x => ‖K x p - K x p₀‖ < ε) fun y _ => ?_
    have h1 : Continuous fun z : P × Mx D m n => ‖K z.2 z.1 - K z.2 p₀‖ :=
      ((hc.comp (continuous_snd.prodMk continuous_fst)).sub
        (hc.comp (continuous_snd.prodMk continuous_const))).norm
    exact (isOpen_lt h1 continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [h] with p h x
  obtain ⟨γ, hγ, hx⟩ := hCc x
  rw [← hp γ hγ x p, ← hp γ hγ x p₀]
  exact (h _ hx).le

theorem isCovolOne_map {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕)
    (e : Mx D m n ≃+ Mx D m n) (he : Continuous e) (he' : Continuous e.symm)
    (hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) :
    IsCovolOne (ratMx D m n) (μ.map e) (e '' 𝓕) ∧ MeasurableEmbedding e := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := h.1
  let f : Mx D m n ≃ₜ Mx D m n := { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hemb : MeasurableEmbedding e := f.measurableEmbedding
  refine ⟨⟨e.isAddHaarMeasure_map μ he he', ?_, ?_⟩, hemb⟩
  · let g : ratMx D m n ≃ ratMx D m n :=
      { toFun := fun γ => ⟨e.symm γ, (hr _).1 (by rw [e.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨e γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (e.symm_apply_apply _) }
    refine h.2.1.image_of_equiv e.toEquiv ?_ g fun γ x => ?_
    · refine ⟨he'.measurable, ?_⟩
      have : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map he'.measurable he.measurable]
        have : (e.symm ∘ e : Mx D m n → Mx D m n) = id := funext e.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change e (e.symm γ + x) = γ + e x
      rw [map_add, e.apply_symm_apply]
  · rw [hemb.map_apply, Set.preimage_image_eq _ e.injective]
    exact h.2.2

theorem parCont : ∀ (D : D7) (m n : ℕ) (v : VolM D m n) (P : Type) [TopologicalSpace P] (K : Mx D m n → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ ratMx D m n, ∀ x p, K (γ + x) p = K x p) → (∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ x in v.𝓕, K x p ∂v.μ) ∧ (∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ x, ‖K x p‖ ≤ C) ∧ ∀ (e : Mx D m n ≃+ Mx D m n), Continuous e → Continuous e.symm → (∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n) → ∀ p, ∫ x in v.𝓕, K (e x) p ∂v.μ = ∫ x in v.𝓕, K x p ∂v.μ := by
  intro D m n v P _ K hc hp
  have hx : ∀ p, Continuous fun x => K x p := fun p => hc.comp (continuous_id.prodMk continuous_const)
  have hi : ∀ p, IntegrableOn (fun x => K x p) v.𝓕 v.μ := fun p =>
    covolOne_integrableOn v.covol _ (hx p) fun γ hγ a => hp γ hγ a p
  refine ⟨hi, ?_, fun p₀ => ?_, fun e he he' hr p => ?_⟩
  · refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [eventually_close K hc hp p₀ (half_pos hε)] with p h
    rw [dist_eq_norm, ← integral_sub (hi p) (hi p₀)]
    have h1 : v.μ v.𝓕 = 1 := v.covol.2.2
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := v.μ) (s := v.𝓕) (f := fun x => K x p - K x p₀) (C := ε / 2)
      (by rw [h1]; exact ENNReal.one_lt_top) fun x _ => h x
    rw [Measure.real, h1, ENNReal.toReal_one, mul_one] at h2
    linarith
  · obtain ⟨-, -, -, -, -, C, hC, hCc⟩ := lattice_Mx D m n
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hx p₀).continuousOn
    refine ⟨B + 1, ?_⟩
    filter_upwards [eventually_close K hc hp p₀ one_pos] with p h x
    obtain ⟨γ, hγ, ha⟩ := hCc x
    have h1 : ‖K x p₀‖ ≤ B := by rw [← hp γ hγ x p₀]; exact hB _ ha
    calc ‖K x p‖ = ‖K x p₀ + (K x p - K x p₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖K x p₀‖ + ‖K x p - K x p₀‖ := norm_add_le _ _
      _ ≤ B + 1 := add_le_add h1 (h x)
  · obtain ⟨h1, hemb⟩ := isCovolOne_map v.covol e he he' hr
    rw [← covolOne_integral_eq v.covol h1 (fun x => K x p) fun γ hγ a => hp γ hγ a p,
      hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]

end GlobalTheory.Unf.ParCont
