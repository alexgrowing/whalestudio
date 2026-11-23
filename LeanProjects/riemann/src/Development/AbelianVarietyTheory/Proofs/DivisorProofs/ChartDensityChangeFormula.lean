import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

namespace GlobalTheory.GlueCover

open GlobalTheory.ChartGlue

variable {n : ℕ}

theorem volume_finite (hn : n ≠ 0) {S : Set (V n)} (hS : S.Finite) : volume S = 0 := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Nonempty (Fin n) := inferInstance
  haveI : Nontrivial (V n) := inferInstance
  exact hS.measure_zero volume

section Null

variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem chartMeas_finite (hn : n ≠ 0) (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞)
    {F : Set X} (hF : F.Finite) : chartMeas e ρ F = 0 := by
  rw [chartMeas_apply e ρ hF.measurableSet]
  exact setLIntegral_measure_zero _ _ (volume_finite hn ((hF.inter_of_right _).image _))

theorem glueMeas_finite (hn : n ≠ 0) (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    {F : Set X} (hF : F.Finite) : glueMeas e ρ F = 0 := by
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [chartMeas_finite hn _ _ hF, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) :=
          Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF.measurableSet, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h

end Null

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

set_option autoImplicit false in
open MeasureTheory Set Topology in
open scoped ENNReal in
variable {n : ℕ} in
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A} in
omit [T2Space A] [T2Space B] in

theorem _root_.GlobalTheory.GlueCover.exists_sheet
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (_root_.ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖_root_.GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {z : B}
    (hch : ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {U : Set B} (hUo : IsOpen U) (hzU : z ∈ U) :
    ∃ M : Set B, M ⊆ U ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        _root_.GlobalTheory.ChartGlue.glueMeas e' ρ' (M ∩ m ⁻¹' Q) = _root_.GlobalTheory.ChartGlue.glueMeas e ρ Q := by
  obtain ⟨i, j, hzj, hzi, hcompat⟩ := hch
  have hMo : IsOpen (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) :=
    (hUo.inter (e' j).open_source).inter ((e i).open_source.preimage hm)
  refine ⟨U ∩ (e' j).source ∩ m ⁻¹' (e i).source, fun w hw => hw.1.1, hMo,
    ⟨⟨hzU, hzj⟩, hzi⟩, ?_, ?_⟩
  · have hm_eq : ∀ w ∈ U ∩ (e' j).source ∩ m ⁻¹' (e i).source,
        (e i).symm (e' j w) = m w := by
      intro w hw
      rw [(hcompat w hw.1.2 hw.2).1, (e i).left_inv hw.2]
    have himage : m '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source) =
        (e i).symm '' (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) := by
      rw [Set.image_image]
      exact (Set.image_congr hm_eq).symm
    rw [himage]
    have hS : IsOpen (e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source)) :=
      (e' j).isOpen_image_of_subset_source hMo (fun w hw => hw.1.2)
    refine (e i).symm.isOpen_image_of_subset_source hS ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [OpenPartialHomeomorph.symm_source, (hcompat w hw.1.2 hw.2).1]
    exact (e i).map_source hw.2
  · intro Q hQ hQM
    have hQi : Q ⊆ (e i).source := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hQM hq
      exact hw.2
    have hPm : MeasurableSet (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) :=
      hMo.measurableSet.inter (hm.measurable hQ)
    have hPj : U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q ⊆ (e' j).source :=
      fun w hw => hw.1.1.2
    rw [_root_.GlobalTheory.ChartGlue.glueMeas_apply e' ρ' hd' hρ' j hPm hPj,
      _root_.GlobalTheory.ChartGlue.glueMeas_apply e ρ hd hρ i hQ hQi,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hPm hPj,
      _root_.GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hQ hQi]
    have himg : e' j '' (U ∩ (e' j).source ∩ m ⁻¹' (e i).source ∩ m ⁻¹' Q) = e i '' Q := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨m w, hw.2, ((hcompat w hw.1.1.2 hw.1.2).1).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hQM hq
        exact ⟨w, ⟨hw, hq⟩, (hcompat w hw.1.2 hw.2).1⟩
    rw [himg]
    refine setLIntegral_congr_fun (_root_.GlobalTheory.ChartGlue.measurableSet_image _ hQ hQi) ?_
    rintro v ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hQM hq
    beta_reduce
    rw [(e i).left_inv hw.2, ← (hcompat w hw.1.2 hw.2).1, (e' j).left_inv hw.1.2]
    exact (hcompat w hw.1.2 hw.2).2

theorem exists_evenly_covered
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : T.Finite) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∉ T) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∉ T, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∉ T), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨U, hU, hUd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzT : ∀ z ∈ F, m z ∉ T := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ U z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    exists_sheet hd hρ hd' hρ' hm (hch z (hzT z hz)) (hU z).2 (hU z).1
  choose! M hMU hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ Tᶜ, (isOpen_biInter_finset hMi).inter hT.isClosed.isOpen_compl,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMU z₁ h₁) (hMU z₂ h₂) (hUd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem map_glueMeas (hn : n ≠ 0)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : T.Finite) (hT' : (m ⁻¹' T).Finite) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) :
    Measure.map m (glueMeas e' ρ') = (d : ℝ≥0∞) • glueMeas e ρ := by
  have hW : ∀ x : {x // x ∉ T}, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered hd hρ hd' hρ' hm hT hfib hch x.2
  choose W hWo hxW hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  refine Measure.ext_of_iUnion_eq_univ
    (s := fun o : Option C => o.elim T fun c => W c.1) ?_ fun o => ?_
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ T
    · exact mem_iUnion.2 ⟨none, hx⟩
    · have hmem : x ∈ ⋃ i ∈ C, W i := by
        rw [hCW]
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
      exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
  · cases o with
    | none =>
      show (Measure.map m (glueMeas e' ρ')).restrict T = ((d : ℝ≥0∞) • glueMeas e ρ).restrict T
      rw [Measure.restrict_eq_zero.2, Measure.restrict_eq_zero.2]
      · simp [glueMeas_finite hn e ρ hT]
      · rw [Measure.map_apply hm.measurable hT.measurableSet]
        exact glueMeas_finite hn e' ρ' hT'
    | some c =>
      show (Measure.map m (glueMeas e' ρ')).restrict (W c.1) =
        ((d : ℝ≥0∞) • glueMeas e ρ).restrict (W c.1)
      ext Q hQ
      have hQW := hQ.inter (hWo c.1).measurableSet
      rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
        Measure.map_apply hm.measurable hQW, hWQ c.1 _ hQW inter_subset_right]
      simp

end Cover

theorem glueMeas_univ_of_cover : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A]
    [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A]
    [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B]
    [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞)
    (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) →
    (∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) →
    (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) →
    ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 →
    (∀ x ∉ T, (m ⁻¹' {x}).encard = d) →
    (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) →
    GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by
  intro n hn A B ι κ _ _ _ _ _ _ _ _ _ _ e ρ e' ρ' hd hρ hd' hρ' m hm T hT hT' d _ hfib hch
  have h := map_glueMeas hn hd hρ hd' hρ' hm hT hT' hfib hch
  have h' := congrArg (fun μ : Measure A => μ Set.univ) h
  simpa [Measure.map_apply hm.measurable MeasurableSet.univ] using h'

end GlobalTheory.GlueCover
