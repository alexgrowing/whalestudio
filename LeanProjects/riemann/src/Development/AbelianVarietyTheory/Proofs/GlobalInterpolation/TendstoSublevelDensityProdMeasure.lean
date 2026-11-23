import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SublevelDensity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
private lemma mul_prod_sublevel_add_le_of_fst_sublevel_le {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (m : Measure A) (m' : Measure A') (μ : Measure B) [SFinite m]
    [SFinite m'] [SFinite μ] (n : A → ℝ) (n' : A' → ℝ) (g : B → ℝ) (hn : Measurable n)
    (hn' : Measurable n') (hg : Measurable g) (hn0 : ∀ x, 0 ≤ n x) (hn0' : ∀ x, 0 ≤ n' x)
    (hg0 : ∀ y, 0 ≤ g y) (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {x | n x < s} ≤ b * m' {x | n' x < s}) :
    a * (m.prod μ) {p | n p.1 + g p.2 < r} ≤ b * (m'.prod μ) {p | n' p.1 + g p.2 < r} := by
  have hS : MeasurableSet {p : A × B | n p.1 + g p.2 < r} :=
    measurableSet_lt ((hn.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A' × B | n' p.1 + g p.2 < r} :=
    measurableSet_lt ((hn'.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply_symm hS, Measure.prod_apply_symm hS']
  calc a * ∫⁻ y, m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ
      ≤ ∫⁻ y, a * m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y, b * m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ := by
        refine lintegral_mono fun y => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hy : r ≤ g y
        · have e1 : {x | n x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 x]
          have e2 : {x | n' x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' x]
          rw [e1, e2]
          simp
        · push_neg at hy
          have e1 : {x | n x + g y < r} = {x | n x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          have e2 : {x | n' x + g y < r} = {x | n' x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 y])
    _ = b * ∫⁻ y, m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_right hS')

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
private lemma mul_prod_sublevel_add_le_of_snd_sublevel_le {A B B' : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace B'] (μ : Measure A) (m : Measure B) (m' : Measure B') [SFinite m]
    [SFinite m'] (g : A → ℝ) (n : B → ℝ) (n' : B' → ℝ) (hg : Measurable g) (hn : Measurable n)
    (hn' : Measurable n') (hg0 : ∀ x, 0 ≤ g x) (hn0 : ∀ y, 0 ≤ n y) (hn0' : ∀ y, 0 ≤ n' y)
    (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {y | n y < s} ≤ b * m' {y | n' y < s}) :
    a * (μ.prod m) {p | g p.1 + n p.2 < r} ≤ b * (μ.prod m') {p | g p.1 + n' p.2 < r} := by
  have hS : MeasurableSet {p : A × B | g p.1 + n p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A × B' | g p.1 + n' p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn'.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply hS, Measure.prod_apply hS']
  calc a * ∫⁻ x, m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ
      ≤ ∫⁻ x, a * m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x, b * m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hx : r ≤ g x
        · have e1 : {y | g x + n y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 y]
          have e2 : {y | g x + n' y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' y]
          rw [e1, e2]
          simp
        · push_neg at hx
          have e1 : {y | g x + n y < r} = {y | n y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          have e2 : {y | g x + n' y < r} = {y | n' y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 x])
    _ = b * ∫⁻ x, m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_left hS')

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in

theorem _root_.GlobalTheory.SublevelDensity.tendsto_prod_density : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  intro A₁ E₁ A₂ E₂ _ _ _ _ m₁ l₁ m₂ l₂ _ _ _ _ n₁ N₁ n₂ N₂ c₁ c₂ hn₁ hN₁ hn₂ hN₂ hn₁0 hN₁0
    hn₂0 hN₂0 hc₁ hc₂ hl₁ hl₂ h₁ h₂
  have hG : ∀ r : ℝ, 0 < r → (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ 0 ∧
      (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ ⊤ := by
    intro r hr
    constructor
    · have hsub : {x | N₁ x < r / 2} ×ˢ {y | N₂ y < r / 2} ⊆
          {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} := by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        linarith
      refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos (hl₁ _ (half_pos hr)).1 (hl₂ _ (half_pos hr)).1
    · have hsub : {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} ⊆ {x | N₁ x < r} ×ˢ {y | N₂ y < r} := by
        rintro ⟨x, y⟩ hxy
        simp only [Set.mem_setOf_eq, Set.mem_prod] at hxy ⊢
        constructor <;> linarith [hN₁0 x, hN₂0 y]
      refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (hl₁ r hr).2 (hl₂ r hr).2
  rw [tendsto_order]
  constructor
  · intro a ha
    have hc0 : c₁ * c₂ ≠ 0 := (lt_of_le_of_lt bot_le ha).ne'
    have hc₁0 : c₁ ≠ 0 := left_ne_zero_of_mul hc0
    have hc₂0 : c₂ ≠ 0 := right_ne_zero_of_mul hc0
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ - t) * (c₂ - t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 := (ENNReal.continuous_sub_left hc₁).tendsto 0
      have t2 := (ENNReal.continuous_sub_left hc₂).tendsto 0
      simp only [tsub_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have ha₁ : c₁ - t < c₁ := ENNReal.sub_lt_self hc₁ hc₁0 htpos'.ne'
    have ha₂ : c₂ - t < c₂ := ENNReal.sub_lt_self hc₂ hc₂0 htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).1 _ ha₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).1 _ ha₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → (c₁ - t) * l₁ {x | N₁ x < s} ≤ 1 * m₁ {x | n₁ x < s} := by
      intro s hs hsr
      have hs' : (c₁ - t) < m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → (c₂ - t) * l₂ {x | N₂ x < s} ≤ 1 * m₂ {x | n₂ x < s} := by
      intro s hs hsr
      have hs' : (c₂ - t) < m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le l₁ m₁ m₂ N₁ n₁ n₂ hN₁ hn₁ hn₂ hN₁0 hn₁0 hn₂0 _ 1 r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ l₂ m₂ N₁ N₂ n₂ hN₁ hN₂ hn₂ hN₁0 hN₂0 hn₂0 _ 1 r k₂
    rw [one_mul] at s₁ s₂
    have key : ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≤
        (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} :=
      calc ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}
          = (c₁ - t) * ((c₂ - t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) := mul_assoc _ _ _
        _ ≤ (c₁ - t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := by gcongr
        _ ≤ (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} := s₁
    exact lt_of_lt_of_le ht
      ((ENNReal.le_div_iff_mul_le (Or.inl (hG r hr0).1) (Or.inl (hG r hr0).2)).2 key)
  · intro b hb
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ + t) * (c₂ + t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 : Tendsto (fun t : ℝ≥0∞ => c₁ + t) (𝓝 0) (𝓝 (c₁ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      have t2 : Tendsto (fun t : ℝ≥0∞ => c₂ + t) (𝓝 0) (𝓝 (c₂ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have hb₁ : c₁ < c₁ + t := ENNReal.lt_add_right hc₁ htpos'.ne'
    have hb₂ : c₂ < c₂ + t := ENNReal.lt_add_right hc₂ htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).2 _ hb₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).2 _ hb₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → 1 * m₁ {x | n₁ x < s} ≤ (c₁ + t) * l₁ {x | N₁ x < s} := by
      intro s hs hsr
      have hs' : m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} < c₁ + t :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → 1 * m₂ {x | n₂ x < s} ≤ (c₂ + t) * l₂ {x | N₂ x < s} := by
      intro s hs hsr
      have hs' : m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} < c₂ + t :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le m₁ l₁ m₂ n₁ N₁ n₂ hn₁ hN₁ hn₂ hn₁0 hN₁0 hn₂0 1 _ r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ m₂ l₂ N₁ n₂ N₂ hN₁ hn₂ hN₂ hN₁0 hn₂0 hN₂0 1 _ r k₂
    rw [one_mul] at s₁ s₂
    have key : (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} ≤
        ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
      calc (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r}
          ≤ (c₁ + t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := s₁
        _ ≤ (c₁ + t) * ((c₂ + t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) :=
          by gcongr
        _ = ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
          (mul_assoc _ _ _).symm
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul key) ht

end GlobalTheory.SublevelDensity
