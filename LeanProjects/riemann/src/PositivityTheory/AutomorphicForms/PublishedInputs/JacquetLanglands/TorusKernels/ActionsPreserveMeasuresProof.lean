import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk

theorem count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Function.Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply ((Set.to_countable _).measurableSet)]
  congr 1
  exact Set.encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ Set.subset_univ s)

theorem countable_PG (F : Type) [Field F] [Countable F] : Countable (PG F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun a b h => Units.ext h
  exact QuotientGroup.mk_surjective.countable

theorem smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (g : GL (Fin 2) F) (z : D.Xs) :
    ((g : PG F) • z) = (fun v => D.r v g • z v : I → P) := rfl

end UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk.ActionsPreserveMeasuresLemmas in
theorem UpperTheory.Esk.actions_preserve_measures_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a := by
  intro h1 h2 h3 F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := h1.1
  have : (volume : Measure P).IsOpenPosMeasure := h1.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) := countable_PG F
  have : Countable D.Om := ax.cO
  have : Countable D.Cj := hPG
  have hXs : SigmaFinite (volume : Measure D.Xs) :=
    show SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)) from inferInstance
  have presX : ∀ γ : PG F, MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact measurePreserving_pi (fun _ : I => (volume : Measure P)) (fun _ : I => (volume : Measure P))
      (fun v => (h1.2.2 (D.r v g)).2)
  have contX : ∀ γ : PG F, Continuous fun z : D.Xs => γ • z := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact continuous_pi fun v => (h1.2.2 (D.r v g)).1.comp (continuous_apply v)
  refine ⟨hPG, hXs, presX, ?_, ?_, contX, inferInstanceAs (BorelSpace (I → P)), ?_⟩
  · intro γ
    exact (count_pres (fun ω : D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro γ
    exact (count_pres (fun ω : D.Cj × D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro δ hδ
    have hk : Continuous fun p : P × P => kap p.1 p.2 := h3.2.2.2.2.1
    have hk1 : ∀ z : P, Continuous fun w => kap z w := fun z => hk.comp (continuous_const.prodMk continuous_id)
    set U : Set P := {w | δ < kap iP w} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const (hk1 iP)
    have hUp : 0 < volume U := hUo.measure_pos volume ⟨iP, by
      show δ < kap iP iP
      rw [h3.2.1 iP]; exact hδ⟩
    obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
    have hS : ∀ z : P, MeasurableSet {w | δ ≤ kap z w} := fun z =>
      measurableSet_le measurable_const (hk1 z).measurable
    have hball : ∀ z : P, (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
      intro z
      obtain ⟨g, -, -, hg⟩ := h3.2.2.2.2.2 z
      have hf := (h1.2.2 g).2
      have hpre : (fun w : P => g • w) ⁻¹' {w | δ ≤ kap z w} = {w | δ ≤ kap iP w} := by
        ext w
        show δ ≤ kap z (g • w) ↔ δ ≤ kap iP w
        rw [← hg, h2.2.2.2.1 g iP w]
      rw [← hf.measure_preimage (hS z).nullMeasurableSet, hpre]
      refine hc0U.le.trans (measure_mono fun w hw => ?_)
      exact le_of_lt (show δ < kap iP w from hw)
    refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
    have hset : {w : X I | Near δ z w} = Set.univ.pi fun v => {w | δ ≤ kap (z v) w} := by
      ext w
      simp [Near, Set.mem_pi]
    rw [hset]
    refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
    rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v _ => hball (z v)
