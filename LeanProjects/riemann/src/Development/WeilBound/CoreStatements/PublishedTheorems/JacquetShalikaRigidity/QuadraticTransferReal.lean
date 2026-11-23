import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferReal

theorem swap3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ρ : Measure β) (ν : Measure γ) [SFinite μ] [SFinite ρ] [SFinite ν]
    (F : α → β → γ → ℝ≥0∞) (hF : Measurable fun p : α × β × γ => F p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, F g r h ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, F g r h ∂μ ∂ν ∂ρ := by
  have h1 : Measurable fun q : α × β => ∫⁻ h, F q.1 q.2 h ∂ν := by
    have : Measurable fun p : (α × β) × γ => F p.1.1 p.1.2 p.2 :=
      hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun g r => ∫⁻ h, F g r h ∂ν) h1.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : α × γ => F q.1 r q.2 :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_lintegral_swap (f := fun g h => F g r h) h2.aemeasurable

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem q1' (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H)
    (hβ : IsWt ν β) (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm := hβ.1
  have hm : Measurable fun p : G × G × G => β p.1 * Φ p.1 * β₁ (p.2.1⁻¹ * p.2.2 * p.1) := by fun_prop
  have hm' : Measurable fun p : G × G × G => β₁ p.1 * (Φ (p.2.1 * p.1) * β (p.2.2⁻¹ * p.2.1 * p.1)) := by
    fun_prop
  have hint : ∀ x, ∫⁻ h, β (h⁻¹ * x) ∂ν = 1 := by
    intro x
    have := lintegral_map (f := fun h => β (h * x)) (g := fun h : G => h⁻¹) (μ := ν)
      (hβm.comp (measurable_mul_const x)) measurable_inv
    rw [hinv, hβ.2 x] at this
    exact this.symm
  have hR : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
    have : Measurable fun p : G × G => Φ (p.2 * p.1) := hΦ.comp (measurable_snd.mul measurable_fst)
    exact this.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hΦ, lintegral_withDensity_eq_lintegral_mul _ hβ₁ hR]
  calc ∫⁻ g, (β * Φ) g ∂μ
      = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hr : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        have e : ∀ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν = β g * Φ g * ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          intro r
          exact lintegral_const_mul _ (by fun_prop)
        simp only [e, Pi.mul_apply]
        rw [lintegral_const_mul _ hr, h1 g, mul_one]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 μ ρ ν (fun g r h => β g * Φ g * β₁ (r⁻¹ * h * g)) hm
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae ?_
        filter_upwards [hH] with h hh
        rw [← lintegral_mul_left_eq_self _ (h⁻¹ * r)]
        refine lintegral_congr fun g => ?_
        have e1 : r⁻¹ * h * (h⁻¹ * r * g) = g := by group
        have e2 : Φ (h⁻¹ * r * g) = Φ (r * g) := by
          have := hΦH h hh (h⁻¹ * (r * g))
          rw [mul_inv_cancel_left] at this
          rw [mul_assoc]
          exact this.symm
        simp only [e1, e2]
        ring
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν ∂ρ ∂μ :=
        (swap3 μ ρ ν (fun g r h => β₁ g * (Φ (r * g) * β (h⁻¹ * r * g))) hm').symm
    _ = ∫⁻ g, (β₁ * fun g => ∫⁻ r, Φ (r * g) ∂ρ) g ∂μ := by
        refine lintegral_congr fun g => ?_
        have e : ∀ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν = β₁ g * Φ (r * g) := by
          intro r
          simp_rw [← mul_assoc (β₁ g)]
          rw [lintegral_const_mul _ (by fun_prop)]
          simp_rw [mul_assoc _ r g]
          rw [hint, mul_one]
        simp only [e, Pi.mul_apply]
        exact lintegral_const_mul _ (hΦ.comp (measurable_mul_const g))

end

theorem real_transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (F : X → ℝ) (hi : Integrable F A) (hiB : Integrable (fun y => F (m y)) B)
    (h₁ : ∫⁻ x, ENNReal.ofReal (F x) ∂A = ∫⁻ y, ENNReal.ofReal (F (m y)) ∂B)
    (h₂ : ∫⁻ x, ENNReal.ofReal (-F x) ∂A = ∫⁻ y, ENNReal.ofReal (-F (m y)) ∂B) :
    ∫ x, F x ∂A = ∫ y, F (m y) ∂B := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiB, h₁, h₂]

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (hm : Measurable m) (Φ : X → ℂ) (hΦ : Measurable Φ) (P : (X → ℝ≥0∞) → Prop)
    (hP : ∀ f, Measurable f → P f → ∫⁻ x, f x ∂A = ∫⁻ y, f (m y) ∂B)
    (hn : P fun x => ‖Φ x‖ₑ) (hr₁ : P fun x => ENNReal.ofReal (Φ x).re)
    (hr₂ : P fun x => ENNReal.ofReal (-(Φ x).re)) (hi₁ : P fun x => ENNReal.ofReal (Φ x).im)
    (hi₂ : P fun x => ENNReal.ofReal (-(Φ x).im)) (hi : Integrable Φ A) :
    Integrable (fun y => Φ (m y)) B ∧ ∫ x, Φ x ∂A = ∫ y, Φ (m y) ∂B := by
  have hiB : Integrable (fun y => Φ (m y)) B := by
    refine ⟨(hΦ.comp hm).aestronglyMeasurable, ?_⟩
    have := hP _ (by fun_prop) hn
    rw [HasFiniteIntegral, ← this]
    exact hi.2
  refine ⟨hiB, ?_⟩
  apply Complex.ext
  · have a1 := integral_re hi
    have a2 := integral_re hiB
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).re) hi.re hiB.re
      (hP _ (by fun_prop) hr₁) (hP _ (by fun_prop) hr₂)
  · have a1 := integral_im hi
    have a2 := integral_im hiB
    simp only [RCLike.im_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).im) hi.im hiB.im
      (hP _ (by fun_prop) hi₁) (hP _ (by fun_prop) hi₂)

end QuadraticTransferReal

theorem closedSubgroup_cutoff_exists : Q2 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH hi
  have hm : Measurable fun p : G × G => p.2 * p.1 := measurable_snd.mul measurable_fst
  have key := QuadraticTransferReal.transfer (μ.withDensity β) ((μ.withDensity β₁).prod ρ) (fun p : G × G => p.2 * p.1) hm Φ hΦ
    (fun f => ∀ h ∈ H, ∀ g, f (h * g) = f g)
    (fun f hf hfH => by
      rw [QuadraticTransferReal.q1' μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 f hf hfH, lintegral_prod (fun p : G × G => f (p.2 * p.1)) (hf.comp hm).aemeasurable])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) hi
  obtain ⟨hiB, he⟩ := key
  refine ⟨hiB.integral_prod_left, ?_⟩
  rw [he, integral_prod _ hiB]

end PositivityTheory.AdelicQuotientData

end
