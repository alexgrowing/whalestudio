import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UpperTheory.Esk.SummedOrbitIntegrals

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

theorem meas_pair [Countable α] {E : Type*} [MeasurableSpace E] {f : α → β → E} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have e : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a : α, ({a} : Set α) ×ˢ (f a ⁻¹' s) := by
    ext ⟨a, b⟩
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hs)

theorem lint_pair (μ : Measure β) [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂(Measure.count.prod μ) = ∑' a, ∫⁻ y, f (a, y) ∂μ := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_count]

theorem count_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  refine Measure.ext_iff_singleton.2 fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

end UpperTheory.Esk.SummedOrbitIntegrals

open UpperTheory.Esk.SummedOrbitIntegrals in
theorem UpperTheory.Esk.pf_Fsum : UpperTheory.Esk.E0a → UpperTheory.Esk.Fsum := by
  intro h0 F I Gf _ _ _ D hax
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  haveI : Countable D.Cj := hcG
  haveI : Countable D.Om := hax.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : SFinite D.μY := by unfold UpperTheory.Esk.Dat.μY; infer_instance
  intro b hb
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun p => hb.nonneg _,
    fun p => hb.sum (p.1.2, p.2)⟩, ?_⟩
  intro u hu hfin
  have hgm : Measurable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) :=
    meas_pair (f := fun (c : D.Cj) (y : D.Y) => b y • u (D.el c) y) fun c => hb.meas.smul (hu (D.el c))
  have hlin : ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) =
      ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
    calc ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY)
        = ∑' c : D.Cj, ∫⁻ y, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          lint_pair D.μY (fun q : D.Cj × D.Y => ‖b q.2 • u (D.el q.1) q.2‖ₑ) hgm.enorm
      _ = ∫⁻ y, ∑' c : D.Cj, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          (lintegral_tsum fun c => ((hb.meas.smul (hu (D.el c))).enorm).aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
          refine lintegral_congr fun y => ?_
          simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]
          exact ENNReal.tsum_mul_left
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ⊤
    rw [hlin]
    exact hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    have hy' : Integrable (fun c : D.Cj => b y • u (D.el c) y) Measure.count := hy
    rw [integral_countable' hy']
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact tsum_const_smul'' (b y)
  have hP : Integrable (fun y => b y • ∑' γ, u γ y) D.μY := hgi.integral_prod_right.congr hae
  have hm1 : Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) :=
    meas_pair (α := D.Cj × D.Om) (β := D.Xs) (f := fun a z => u (D.el a.1) (a.2, z))
      fun a => (hu (D.el a.1)).comp measurable_prodMk_left
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs)
      D.μC (Measure.count.prod D.μY) := by
    have e : D.μC = (Measure.count.prod Measure.count).prod volume := by
      unfold UpperTheory.Esk.Dat.μC
      rw [count_prod]
    rw [e]
    exact measurePreserving_prodAssoc _ _ _
  have hC : Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  have hint : ∫ y, b y • ∑' γ, u γ y ∂D.μY =
      ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC := by
    calc ∫ y, b y • ∑' γ, u γ y ∂D.μY
        = ∫ y, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) ∂D.μY := (integral_congr_ae hae).symm
      _ = ∫ q, b q.2 • u (D.el q.1) q.2 ∂(Measure.count.prod D.μY) := (integral_prod_symm _ hgi).symm
      _ = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC :=
          (hmp.integral_comp' (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2)).symm
  exact ⟨hm1, hC, hP, hint⟩
