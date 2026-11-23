import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure

open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FactS.OpenFactor

section Generic

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) : (μ.comap e).map e = μ := by
  rw [he.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hμ)

theorem comap_invariant {e : Y → X} (he : MeasurableEmbedding e) {a : X → X} {a' : Y → Y}
    (ha : Measurable a) (ha' : Measurable a') (hcomm : ∀ y, e (a' y) = a (e y)) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (hinv : μ.map a = μ) : (μ.comap e).map a' = μ.comap e := by
  have hν := map_comap_of_carried he hμ
  have h2 : ((μ.comap e).map a').map e = μ := by
    rw [Measure.map_map he.measurable ha']
    have h3 : e ∘ a' = a ∘ e := funext hcomm
    rw [h3, ← Measure.map_map ha he.measurable, hν, hinv]
  have h4 := he.comap_map ((μ.comap e).map a')
  rw [h2] at h4
  exact h4.symm

theorem lintegral_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (G : X → ℝ≥0∞) :
    ∫⁻ y, G (e y) ∂(μ.comap e) = ∫⁻ x, G x ∂μ := by
  rw [← he.lintegral_map, map_comap_of_carried he hμ]

theorem comap_ne_zero_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (h0 : μ ≠ 0) : μ.comap e ≠ 0 := by
  intro h
  have h1 := map_comap_of_carried he hμ
  rw [h, Measure.map_zero] at h1
  exact h0 h1.symm

theorem comap_finite_compacts [TopologicalSpace X] [TopologicalSpace Y] {e : Y → X}
    (he : MeasurableEmbedding e) (hc : Continuous e) {S : Set X} (hS : ∀ y, e y ∈ S)
    {μ : Measure X} (hfin : ∀ K, IsCompact K → K ⊆ S → μ K < ⊤) :
    IsFiniteMeasureOnCompacts (μ.comap e) :=
  ⟨fun K hK => by
    rw [he.comap_apply]
    exact hfin _ (hK.image hc) (by rintro _ ⟨y, -, rfl⟩; exact hS y)⟩

end Generic

theorem prod_factor_open : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  intro ι _ G₀ _ _ _ _ _ _ G _ _ _ _ _ _ W₀ _ _ _ _ _ _ W _ _ _ _ _ _
    a₀ a hc₀ h1₀ hm₀ hc h1 hm U₀ U hU₀ hU hsU₀ hsU Z₀ Z hZ₀ hZ hs₀ hs ht₀ ht m₀ m hfin₀ hfin
    hi₀ hi hz₀ hz hn₀ hn P hPc hP hPZ
  classical
  haveI : LocallyCompactSpace ↥U₀ := hU₀.locallyCompactSpace
  haveI : ∀ i, LocallyCompactSpace ↥(U i) := fun i => (hU i).locallyCompactSpace
  have hmeas₀ : ∀ g, Measurable (a₀ g) := fun g =>
    (hc₀.comp (Continuous.prodMk_right g)).measurable
  have hmeas : ∀ i g, Measurable (a i g) := fun i g =>
    ((hc i).comp (Continuous.prodMk_right g)).measurable
  let b₀ : G₀ → ↥U₀ → ↥U₀ := fun g x => ⟨a₀ g x.1, hsU₀ g x.1 x.2⟩
  let b : ∀ i, G i → ↥(U i) → ↥(U i) := fun i g x => ⟨a i g x.1, hsU i g x.1 x.2⟩
  let E : (↥U₀ × ∀ i, ↥(U i)) → W₀ × ∀ i, W i := Prod.map Subtype.val fun z i => (z i).1
  have he₀ : MeasurableEmbedding (Subtype.val : ↥U₀ → W₀) :=
    MeasurableEmbedding.subtype_coe hU₀.measurableSet
  have he : ∀ i, MeasurableEmbedding (Subtype.val : ↥(U i) → W i) := fun i =>
    MeasurableEmbedding.subtype_coe (hU i).measurableSet
  have hEo : IsOpenEmbedding E :=
    hU₀.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.piMap fun i => (hU i).isOpenEmbedding_subtypeVal)
  have hE : MeasurableEmbedding E := hEo.measurableEmbedding
  have hcar₀ : m₀ (Set.range (Subtype.val : ↥U₀ → W₀))ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hz₀
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcar : ∀ i, m i (Set.range (Subtype.val : ↥(U i) → W i))ᶜ = 0 := fun i => by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hz i)
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcarP : P (Set.range E)ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hPZ
    rintro ⟨x, z⟩ ⟨h₀, hz'⟩
    exact ⟨(⟨x, h₀.2⟩, fun i => ⟨z i, (hz' i (Set.mem_univ i)).2⟩), rfl⟩
  haveI : IsFiniteMeasureOnCompacts (m₀.comap (Subtype.val : ↥U₀ → W₀)) :=
    comap_finite_compacts he₀ continuous_subtype_val (fun y => y.2) (hfin₀)
  haveI : ∀ i, IsFiniteMeasureOnCompacts ((m i).comap (Subtype.val : ↥(U i) → W i)) := fun i =>
    comap_finite_compacts (he i) continuous_subtype_val (fun y => y.2) (hfin i)
  haveI : IsFiniteMeasureOnCompacts (P.comap E) :=
    comap_finite_compacts hE hEo.continuous (S := Set.univ) (fun _ => Set.mem_univ _)
      (fun K hK _ => hK.measure_lt_top)
  have hcb₀ : Continuous fun p : G₀ × ↥U₀ => b₀ p.1 p.2 :=
    Continuous.subtype_mk (hc₀.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hcb : ∀ i, Continuous fun p : G i × ↥(U i) => b i p.1 p.2 := fun i =>
    Continuous.subtype_mk ((hc i).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hmb₀ : ∀ g, Measurable (b₀ g) := fun g =>
    (hcb₀.comp (Continuous.prodMk_right g)).measurable
  have hmb : ∀ i g, Measurable (b i g) := fun i g =>
    ((hcb i).comp (Continuous.prodMk_right g)).measurable
  obtain ⟨c, hcf⟩ := prod_factor (G₀ := G₀) (G := G) (W₀ := ↥U₀) (W := fun i => ↥(U i)) b₀ b
    hcb₀ (fun x => Subtype.ext (h1₀ x.1)) (fun g h x => Subtype.ext (hm₀ g h x.1))
    hcb (fun i x => Subtype.ext (h1 i x.1)) (fun i g h x => Subtype.ext (hm i g h x.1))
    (Subtype.val ⁻¹' Z₀) (fun i => Subtype.val ⁻¹' Z i)
    (hZ₀.preimage continuous_subtype_val) (fun i => (hZ i).preimage continuous_subtype_val)
    (fun g x hx => hs₀ g x.1 hx) (fun i g x hx => hs i g x.1 hx)
    (fun x hx y hy => by
      obtain ⟨g, hg⟩ := ht₀ x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (fun i x hx y hy => by
      obtain ⟨g, hg⟩ := ht i x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (m₀.comap Subtype.val) (fun i => (m i).comap Subtype.val)
    (fun g => comap_invariant he₀ (hmeas₀ g) (hmb₀ g) (fun _ => rfl) hcar₀ (hi₀ g))
    (fun i g => comap_invariant (he i) (hmeas i g) (hmb i g) (fun _ => rfl) (hcar i) (hi i g))
    (by
      rw [he₀.comap_apply]
      refine measure_mono_null ?_ hz₀
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun i => by
      rw [(he i).comap_apply]
      refine measure_mono_null ?_ (hz i)
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun ⟨x, hx⟩ => comap_ne_zero_of_carried he₀ hcar₀ (hn₀ ⟨x.1, hx, x.2⟩))
    (fun i ⟨x, hx⟩ => comap_ne_zero_of_carried (he i) (hcar i) (hn i ⟨x.1, hx, x.2⟩))
    (P.comap E)
    (fun g₀ g => comap_invariant hE
      (a := fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i)))
      ((hmeas₀ g₀).comp measurable_fst |>.prodMk (measurable_pi_lambda _ fun i =>
        (hmeas i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      ((hmb₀ g₀).comp measurable_fst |>.prodMk (measurable_pi_lambda _ fun i =>
        (hmb i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      (fun _ => rfl) hcarP (hP g₀ g))
    (by
      rw [hE.comap_apply]
      refine measure_mono_null ?_ hPZ
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy ⟨hmem.1.1, fun i _ => (hmem.2 i (Set.mem_univ i)).1⟩)
  refine ⟨c, fun f₀ f hf₀ hf => ?_⟩
  have h := hcf (fun x => f₀ x.1) (fun i x => f i x.1) (hf₀.comp measurable_subtype_coe)
    (fun i => (hf i).comp measurable_subtype_coe)
  have hL := lintegral_comap_of_carried hE hcarP fun x => f₀ x.1 * ∏ i, f i (x.2 i)
  have hL₀ := lintegral_comap_of_carried he₀ hcar₀ f₀
  have hLi := fun i => lintegral_comap_of_carried (he i) (hcar i) (f i)
  rw [← hL, ← hL₀]
  simp only [← hLi]
  exact h

end GlobalTheory.CompanionTheory.SW.FactS.OpenFactor
