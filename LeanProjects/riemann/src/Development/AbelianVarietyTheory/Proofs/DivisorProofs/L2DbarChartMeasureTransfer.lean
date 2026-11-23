import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt

namespace GlobalTheory.GlueCoverNull

open Set Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.GlueCover
open scoped ENNReal

variable {n : ℕ}

theorem glueMeas_null {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    {F : Set X} (hF : MeasurableSet F) (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
    glueMeas e ρ F = 0 := by
  have hc : ∀ i, chartMeas (e i) (ρ i) F = 0 := fun i => by
    rw [chartMeas_apply (e i) (ρ i) hF]
    exact setLIntegral_measure_zero _ _ (h0 i)
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) :=
          Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T) {d : ℕ}
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
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ Tᶜ, (isOpen_biInter_finset hMi).inter hT.isOpen_compl,
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

theorem map_glueMeas_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T)
    (hT0 : ∀ i, volume ((e i) '' ((e i).source ∩ T)) = 0)
    (hT0' : ∀ j, volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) :
    Measure.map m (glueMeas e' ρ') = (d : ℝ≥0∞) • glueMeas e ρ := by
  have hW : ∀ x : {x // x ∉ T}, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_closed hd hρ hd' hρ' hm hT hfib hch x.2
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
      · simp [glueMeas_null e ρ hT.measurableSet hT0]
      · rw [Measure.map_apply hm.measurable hT.measurableSet]
        exact glueMeas_null e' ρ' (hT.preimage hm).measurableSet hT0'
    | some c =>
      show (Measure.map m (glueMeas e' ρ')).restrict (W c.1) =
        ((d : ℝ≥0∞) • glueMeas e ρ).restrict (W c.1)
      ext Q hQ
      have hQW := hQ.inter (hWo c.1).measurableSet
      rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
        Measure.map_apply hm.measurable hQW, hWQ c.1 _ hQW inter_subset_right]
      simp

end Cover

theorem map_glueMeas_of_cover : ∀ (n : ℕ) (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ENNReal) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ENNReal), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, IsClosed T → (∀ i, MeasureTheory.volume ((e i) '' ((e i).source ∩ T)) = 0) → (∀ j, MeasureTheory.volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) → ∀ d : ℕ, (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → MeasureTheory.Measure.map m (GlobalTheory.ChartGlue.glueMeas e' ρ') = (d : ENNReal) • GlobalTheory.ChartGlue.glueMeas e ρ := by
  intro n A B ι κ _ _ _ _ _ _ _ _ _ _ e ρ e' ρ' hd hρ hd' hρ' m hm T hT hT0 hT0' d hfib hch
  exact map_glueMeas_closed hd hρ hd' hρ' hm hT hT0 hT0' hfib hch

end GlobalTheory.GlueCoverNull
