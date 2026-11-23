import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsInt

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem weil_inv {μ μS ν : Measure G} [SFinite μS] [SFinite ν]
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) (Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, ∫⁻ s, Ψ (s⁻¹ * z) ∂μS ∂ν = ∫⁻ x, Ψ x ∂μ := by
  rw [hW Ψ hΨ]
  refine lintegral_congr fun z => ?_
  have hm : Measurable (fun s : G => Ψ (s * z)) := hΨ.comp (measurable_id.mul measurable_const)
  conv_rhs => rw [← hinv]
  rw [lintegral_map hm measurable_inv]

variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']

@[irreducible] def PhiGG (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ : G) (a b : G) : ℝ≥0∞ :=
  ‖⟪σ a w, σ γ (σ b w)⟫_ℂ‖ₑ * ‖W a‖ₑ * ‖W' b‖ₑ

theorem measurable_PhiGG {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : G × G => PhiGG σ w W W' γ p.1 p.2) := by
  unfold PhiGG
  have h1 : Continuous (fun p : G × G => ⟪σ p.1 w, σ γ (σ p.2 w)⟫_ℂ) :=
    Continuous.inner (𝕜 := ℂ) ((hσ.2.2.2 w).comp continuous_fst)
      ((σ γ).continuous.comp ((hσ.2.2.2 w).comp continuous_snd))
  exact ((h1.enorm.measurable).mul ((hW.comp continuous_fst).enorm.measurable)).mul
    ((hW'.comp continuous_snd).enorm.measurable)

theorem quad_eq_GG {μ μS ν μS' ν' : Measure G} [SFinite μS] [SFinite ν] [SFinite μS'] [SFinite ν'] [SFinite μ]
    {S S' : Set G} {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hWc : Continuous W) (hWc' : Continuous W')
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hWe' : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS' ∂ν')
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (hiS : ∀ a ∈ S, a⁻¹ ∈ S) (hiS' : ∀ a ∈ S', a⁻¹ ∈ S')
    (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) (hWS' : ∀ s ∈ S', ∀ x, ‖W' (s * x)‖ = ‖W' x‖) (γ : G) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS ∂ν' ∂ν =
      ∫⁻ x, ∫⁻ y, PhiGG σ w W W' γ x y ∂μ ∂μ := by
  have hΦ := measurable_PhiGG hσ w hWc hWc' γ

  have hpt : ∀ z z' s s', s ∈ S → s' ∈ S' →
      ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ = PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') := by
    intro z z' s s' hs hs'
    unfold PhiGG
    rw [coef_shift hσ w γ z s z' s']
    have e1 : ‖W (s⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS _ (hiS s hs)]
    have e2 : ‖W' (s'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS' _ (hiS' s' hs')]
    rw [e1, e2]
  have haeS : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have haeS' : ∀ᵐ s ∂μS', s ∈ S' := by rw [ae_iff]; exact h0'
  have hin : ∀ z z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS =
      ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS := by
    intro z z'
    refine lintegral_congr_ae ?_
    filter_upwards [haeS] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [haeS'] with s' hs'
    exact hpt z z' s s' hs hs'
  simp only [hin]

  have hswap : ∀ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS ∂ν' =
      ∫⁻ s, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂ν' ∂μS := by
    intro z
    have hm : Measurable (Function.uncurry fun z' s : G => ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS') := by
      have hg : Measurable (fun q : (G × G) × G => ((q.1.2⁻¹ * z, q.2⁻¹ * q.1.1) : G × G)) :=
        (((measurable_snd.comp measurable_fst).inv.mul measurable_const)).prodMk
          ((measurable_snd.inv).mul (measurable_fst.comp measurable_fst))
      have h3 : Measurable (fun q : (G × G) × G => PhiGG σ w W W' γ (q.1.2⁻¹ * z) (q.2⁻¹ * q.1.1)) :=
        hΦ.comp hg
      exact h3.lintegral_prod_right'
    exact lintegral_lintegral_swap hm.aemeasurable
  simp only [hswap]

  have hy : ∀ a, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ a (s'⁻¹ * z') ∂μS' ∂ν' = ∫⁻ y, PhiGG σ w W W' γ a y ∂μ := by
    intro a
    exact weil_inv hWe' hinv' (fun y => PhiGG σ w W W' γ a y) (hΦ.comp (measurable_const.prodMk measurable_id))
  simp only [hy]

  have hmy : Measurable (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) := hΦ.lintegral_prod_right'
  exact weil_inv hWe hinv (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) hmy

theorem triple_lintegral_eq {μ μS ν : Measure G} [SFinite μS] [SFinite ν] {S : Set G} {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (h0 : μS Sᶜ = 0) (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν =
      ∫⁻ z, ‖W z‖ₑ * ∫⁻ y, ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ ∂μ ∂ν := by
  refine lintegral_congr fun z => ?_
  set H : G → ℝ≥0∞ := fun y => ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ with hHdef
  have hHm : Measurable H := by
    have h1 : Continuous (fun y => ⟪σ z w, σ y w⟫_ℂ) := Continuous.inner (𝕜 := ℂ) continuous_const (hσ.2.2.2 w)
    exact (h1.enorm.measurable).mul hWc.enorm.measurable
  have hae : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have hin : ∀ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS =
      ‖W z‖ₑ * ∫⁻ s, H (s * z') ∂μS := by
    intro z'
    rw [← lintegral_const_mul (‖W z‖ₑ) (f := fun s => H (s * z')) (hHm.comp (measurable_mul_const z'))]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    simp only [hHdef]
    have e1 : σ s (σ z' w) = σ (s * z') w := (rep_mul_apply hσ s z' w)
    have e2 : ‖W z'‖ₑ = ‖W (s * z')‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS s hs z']
    rw [e1, e2]
    ring
  simp only [hin]
  have hmeas : Measurable (fun z' : G => ∫⁻ s, H (s * z') ∂μS) := by
    have h2 : Measurable (fun p : G × G => H (p.2 * p.1)) := hHm.comp (measurable_snd.mul measurable_fst)
    exact h2.lintegral_prod_right'
  rw [lintegral_const_mul (‖W z‖ₑ) (f := fun z' => ∫⁻ s, H (s * z') ∂μS) hmeas]
  congr 1
  exact (hWe H hHm).symm

end Formalism.L2.S.Pv.ConvG
