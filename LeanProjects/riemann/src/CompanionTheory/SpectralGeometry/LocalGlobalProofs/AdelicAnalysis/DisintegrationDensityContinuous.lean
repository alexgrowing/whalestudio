import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreFam

section Top

variable {V : Type} [TopologicalSpace V]

theorem exists_bump [LocallyCompactSpace V] [T2Space V] {K O : Set V} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K, φ v = 1 := by
  obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  exact ⟨f, f.continuous, hfc, hfs, fun v => (hf01 v).1, fun v => (hf01 v).2, fun v hv => hf1 hv⟩

theorem exists_exhaustion [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} (hU : IsOpen U) :
    ∃ K W : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ K n) ∧
      (∀ n, K n ⊆ U) ∧ Monotone K ∧ Monotone W ∧ (⋃ n, K n) = U ∧ (⋃ n, W n) = U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have hint : ⋃ n, interior (E n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, E n := by
      rw [E.iUnion_eq]
      exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, E.subset_interior_succ n hn⟩
  refine ⟨fun n => (↑) '' E n, fun n => (↑) '' interior (E n),
    fun n => (E.isCompact n).image continuous_subtype_val,
    fun n => hU.isOpenMap_subtype_val _ isOpen_interior, fun n => Set.image_mono interior_subset,
    fun n => by
      rintro _ ⟨x, -, rfl⟩
      exact x.2,
    fun m n hmn => Set.image_mono (E.subset hmn),
    fun m n hmn => Set.image_mono (interior_mono (E.subset hmn)), ?_, ?_⟩
  · rw [← Set.image_iUnion, E.iUnion_eq, Set.image_univ, Subtype.range_coe]
  · rw [← Set.image_iUnion, hint, Set.image_univ, Subtype.range_coe]

end Top

section Meas

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

theorem le_lintegral_bump [T2Space V] (m : Measure V) {K : Set V} (hK : IsCompact K) {φ : V → ℝ}
    (h0 : ∀ v, 0 ≤ φ v) (h1 : ∀ v ∈ K, φ v = 1) : m K ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [← lintegral_indicator_one hKm]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ K
  · simp [Set.indicator_apply, hv, h1 v hv]
  · simp [Set.indicator_apply, hv]

theorem lintegral_bump_le (m : Measure V) {O : Set V} (hO : IsOpen O) {φ : V → ℝ}
    (h1 : ∀ v, φ v ≤ 1) (hs : tsupport φ ⊆ O) : ∫⁻ v, ENNReal.ofReal (φ v) ∂m ≤ m O := by
  rw [← lintegral_indicator_one hO.measurableSet]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ O
  · simpa [Set.indicator_apply, hv] using h1 v
  · have hz : φ v = 0 := by
      by_contra hne
      exact hv (hs (subset_tsupport φ hne))
    simp [Set.indicator_apply, hv, hz]

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def BumpFamily (U : Set V) (B : Set X) (fib : X → Measure V) : Prop :=
  (∀ b, b ∉ B → fib b = 0) ∧
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ b ∈ B, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B

theorem BumpFamily.measurable_lintegral {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {φ : V → ℝ} (hc : Continuous φ)
    (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  classical
  obtain ⟨h0B, hφ⟩ := h
  obtain ⟨hint, hcont⟩ := hφ φ hc hcs hs
  have heq : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =
      B.piecewise (fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b))) (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ B
    · simp only [Set.piecewise_eq_of_mem, hb]
      rw [ofReal_integral_eq_lintegral_ofReal (hint b hb) (ae_of_all _ h0)]
    · simp [Set.piecewise, hb, h0B b hb]
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).measurable_piecewise continuousOn_const
    hB.measurableSet

theorem BumpFamily.measurable_open [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {O : Set V} (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable fun b => fib b O := by
  obtain ⟨K, W, hKc, -, -, hKO, hKmono, -, hKU, -⟩ := exists_exhaustion hO
  have hφ : ∀ n, ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K n, φ v = 1 := fun n => exists_bump (hKc n) hO (hKO n)
  choose φ hφc hφcs hφs hφ0 hφ1 hφK using hφ
  have hmeas : ∀ n, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ n v) ∂(fib b) := fun n =>
    h.measurable_lintegral hB (hφc n) (hφcs n) ((hφs n).trans hOU) (hφ0 n)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun b => ?_)
  have hlow : Filter.Tendsto (fun n => fib b (K n)) Filter.atTop (𝓝 (fib b O)) := by
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hKmono
    rw [hKU] at h2
    exact h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => le_lintegral_bump (fib b) (hKc n) (hφ0 n) (hφK n))
    (fun n => lintegral_bump_le (fib b) hO (hφ1 n) (hφs n))

theorem BumpFamily.lt_top [LocallyCompactSpace V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hU : IsOpen U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) (b : X) :
    fib b K < ∞ := by
  by_cases hb : b ∈ B
  · obtain ⟨φ, hc, hcs, hs, h0, -, hK1⟩ := exists_bump hK hU hKU
    have hint := (h.2 φ hc hcs hs).1 b hb
    exact lt_of_le_of_lt (le_lintegral_bump (fib b) hK h0 hK1) hint.lintegral_lt_top
  · rw [h.1 b hb]
    simp

theorem BumpFamily.measurable_apply [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) (hU : IsOpen U) (hc : ∀ b, fib b Uᶜ = 0)
    {A : Set V} (hA : MeasurableSet A) : Measurable fun b => fib b A := by
  obtain ⟨K, W, hKc, hWo, hWK, hKU, -, hWmono, -, hWU⟩ := exists_exhaustion hU
  have hWn : ∀ n, Measurable fun b => fib b (A ∩ W n) := by
    intro n
    haveI : ∀ b, IsFiniteMeasure ((fib b).restrict (W n)) := fun b =>
      isFiniteMeasure_restrict.mpr
        (ne_of_lt (lt_of_le_of_lt (measure_mono (hWK n)) (h.lt_top hU (hKc n) (hKU n) b)))
    have hmeas : Measurable fun b => (fib b).restrict (W n) := by
      refine Measurable.measure_of_isPiSystem (S := {s : Set V | IsOpen s}) BorelSpace.measurable_eq
        isPiSystem_isOpen ?_ ?_
      · intro s hs
        have hso : IsOpen s := hs
        simp only [Measure.restrict_apply hso.measurableSet]
        exact h.measurable_open hB (hso.inter (hWo n))
          (Set.inter_subset_right.trans ((hWK n).trans (hKU n)))
      · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact h.measurable_open hB (hWo n) ((hWK n).trans (hKU n))
    have h2 := (Measure.measurable_coe hA).comp hmeas
    simpa [Function.comp_def, Measure.restrict_apply hA] using h2
  have hlim : ∀ b, Filter.Tendsto (fun n => fib b (A ∩ W n)) Filter.atTop (𝓝 (fib b A)) := by
    intro b
    have hmono : Monotone fun n => A ∩ W n := fun m n hmn => Set.inter_subset_inter_right _ (hWmono hmn)
    have h2 := tendsto_measure_iUnion_atTop (μ := fib b) hmono
    rw [← Set.inter_iUnion, hWU, measure_inter_conull (hc b)] at h2
    exact h2
  exact measurable_of_tendsto_metrizable hWn (tendsto_pi_nhds.mpr hlim)

end Meas

theorem fibre_family_basic : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g →
    (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧
    (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧
    ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfv B hB fib hF
  classical
  obtain ⟨hfib0, -, hbump⟩ := hF
  have hU : IsOpen (g ⁻¹' B) := hB.preimage hg
  have hmemι : ∀ b w, w ∈ f ⁻¹' {ι b} → g w = b := by
    intro b w hw
    apply hι
    rw [← hfv w]
    exact hw
  have hfibB : ∀ b, b ∉ B → fib b = 0 := by
    intro b hb
    have hempty : f ⁻¹' {ι b} ∩ g ⁻¹' B = ∅ := by
      refine Set.subset_empty_iff.mp fun w hw => (hb ?_).elim
      rw [← hmemι b w hw.1]
      exact hw.2
    have h0 := hfib0 b
    rw [hempty, Set.compl_empty] at h0
    exact Measure.measure_univ_eq_zero.mp h0
  have hBF : BumpFamily (g ⁻¹' B) B fib := ⟨hfibB, hbump⟩
  refine ⟨?_, hfibB, ?_, ?_⟩
  · intro b
    refine ⟨fun v => ?_⟩
    by_cases hb : b ∈ B
    · by_cases hgv : g v = b
      · have hvU : v ∈ g ⁻¹' B := by
          rw [Set.mem_preimage, hgv]
          exact hb
        obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hvU)
        exact ⟨K, hKn, hBF.lt_top hU hKc hKU b⟩
      · refine ⟨g ⁻¹' {b}ᶜ, (isClosed_singleton.preimage hg).isOpen_compl.mem_nhds hgv, ?_⟩
        have h0 : fib b (g ⁻¹' {b}ᶜ) = 0 := by
          exact measure_mono_null (show g ⁻¹' {b}ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from
            fun w hw hw' => hw (hmemι b w hw'.1)) (hfib0 b)
        rw [h0]
        exact ENNReal.zero_lt_top
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      rw [hfibB b hb]
      simp
  · intro A hA
    exact hBF.measurable_apply hB hU (fun b => measure_mono_null
      (show (g ⁻¹' B)ᶜ ⊆ (f ⁻¹' {ι b} ∩ g ⁻¹' B)ᶜ from fun w hw hw' => hw hw'.2) (hfib0 b)) hA
  · intro C D hC hD hDB
    have hC' : IsCompact (C ∩ g ⁻¹' D) := hC.inter_right (hD.isClosed.preimage hg)
    have hC'U : C ∩ g ⁻¹' D ⊆ g ⁻¹' B := fun w hw => hDB hw.2
    obtain ⟨φ, hc, hcs, hs, h0, -, h1⟩ := exists_bump hC' hU hC'U
    obtain ⟨hint, hcont⟩ := hbump φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hcont.mono hDB)
    refine ⟨Real.toNNReal M, fun b hb => ?_⟩
    calc fib b C = fib b (C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B)) := (measure_inter_conull (hfib0 b)).symm
      _ ≤ fib b (C ∩ g ⁻¹' D) := by
          refine measure_mono (show C ∩ (f ⁻¹' {ι b} ∩ g ⁻¹' B) ⊆ C ∩ g ⁻¹' D from
            fun w hw => ⟨hw.1, ?_⟩)
          show g w ∈ D
          rw [hmemι b w hw.2.1]
          exact hb
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := le_lintegral_bump (fib b) hC' h0 h1
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint b (hDB hb)) (ae_of_all _ h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM b hb))
      _ = (Real.toNNReal M : ℝ≥0∞) := rfl

end GlobalTheory.CompanionTheory.SW.FibreFam
