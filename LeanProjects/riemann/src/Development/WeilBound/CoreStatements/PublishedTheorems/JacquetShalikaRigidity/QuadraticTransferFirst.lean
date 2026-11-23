import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferFirst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem swap3 {μ ν ρ : Measure G} [SFinite μ] [SFinite ν] [SFinite ρ] (K : G → G → G → ℝ≥0∞)
    (hK : Measurable fun p : G × G × G => K p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, K r h g ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, K r h g ∂μ ∂ν ∂ρ := by
  have hF : Measurable (Function.uncurry fun g r => ∫⁻ h, K r h g ∂ν) := by
    have : Measurable fun q : (G × G) × G => K q.1.2 q.2 q.1.1 :=
      hK.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hK' : Measurable (Function.uncurry fun g h => K r h g) :=
    hK.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hK'.aemeasurable

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H) (hβ : IsWt ν β)
    (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) (Φ : G → ℝ≥0∞)
    (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm : Measurable β := hβ.1
  have hH' : ∀ᵐ h ∂ν, h⁻¹ ∈ H := by
    have hH2 := hH
    rw [← hinv] at hH2
    exact ae_of_ae_map measurable_inv.aemeasurable hH2
  have hinvβ : ∀ g, ∫⁻ h, β (h⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h : G => β (h * g) := by fun_prop
    rw [show (∫⁻ h, β (h⁻¹ * g) ∂ν) = ∫⁻ h, β (h * g) ∂(Measure.map (fun h => h⁻¹) ν) from
      (lintegral_map hm measurable_inv).symm, hinv]
    exact hβ.2 g
  calc ∫⁻ g, Φ g ∂μ.withDensity β
      = ∫⁻ g, β g * Φ g ∂μ := lintegral_withDensity_eq_lintegral_mul _ hβm hΦ
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm1 : ∀ r, Measurable fun h => β₁ (r⁻¹ * h * g) := fun r => by fun_prop
        have hm2 : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        calc β g * Φ g = β g * Φ g * ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ := by rw [h1 g, mul_one]
          _ = _ := by
            rw [← lintegral_const_mul _ hm2]
            refine lintegral_congr fun r => ?_
            rw [lintegral_const_mul _ (hm1 r)]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 (fun r h g => β g * Φ g * β₁ (r⁻¹ * h * g))
          (show Measurable fun p : G × G × G => β p.2.2 * Φ p.2.2 * β₁ (p.1⁻¹ * p.2.1 * p.2.2) by fun_prop)
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae (hH'.mono fun h hh => ?_)
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => β x * Φ x * β₁ (r⁻¹ * h * x)) h⁻¹).symm.trans
          (lintegral_congr fun g => ?_)
        show β (h⁻¹ * g) * Φ (h⁻¹ * g) * β₁ (r⁻¹ * h * (h⁻¹ * g)) = _
        rw [hΦH _ hh, mul_assoc r⁻¹ h, mul_inv_cancel_left]
    _ = ∫⁻ r, ∫⁻ g, ∫⁻ h, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂ν ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        exact lintegral_lintegral_swap
          (show Measurable fun p : G × G => β (p.1⁻¹ * p.2) * Φ p.2 * β₁ (r⁻¹ * p.2) by fun_prop).aemeasurable
    _ = ∫⁻ r, ∫⁻ g, Φ g * β₁ (r⁻¹ * g) ∂μ ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun g => ?_
        simp_rw [mul_assoc]
        rw [lintegral_mul_const _ (show Measurable fun h : G => β (h⁻¹ * g) by fun_prop), hinvβ g, one_mul]
    _ = ∫⁻ r, ∫⁻ g, Φ (r * g) * β₁ g ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * β₁ (r⁻¹ * x)) r).symm.trans
          (lintegral_congr fun g => ?_)
        show Φ (r * g) * β₁ (r⁻¹ * (r * g)) = _
        rw [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) * β₁ g ∂ρ ∂μ :=
        lintegral_lintegral_swap
          (show Measurable fun p : G × G => Φ (p.1 * p.2) * β₁ p.2 by fun_prop).aemeasurable
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
        have hm : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
          have : Measurable fun p : G × G => Φ (p.2 * p.1) := by fun_prop
          exact this.lintegral_prod_right'
        rw [lintegral_withDensity_eq_lintegral_mul _ hβ₁ hm]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable fun r : G => Φ (r * g) by fun_prop)]
        exact mul_comm _ _

end QuadraticTransferFirst

theorem isUnit_last_join : Q1 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH
  exact QuadraticTransferFirst.main μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH

end PositivityTheory.AdelicQuotientData

end
