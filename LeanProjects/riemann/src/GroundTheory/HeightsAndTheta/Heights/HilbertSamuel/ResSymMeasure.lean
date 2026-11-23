import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResSym

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

section Normalise

variable {J : Type} [Fintype J]

open Classical in

def NZAt (z : J → ℂ) (k : ℕ) : Prop :=
  ∀ h : k < Fintype.card J, z ((Fintype.equivFin J).symm ⟨k, h⟩) ≠ 0

theorem exists_nzAt (z : J → ℂ) : ∃ k, NZAt z k :=
  ⟨Fintype.card J, fun h => absurd h (lt_irrefl _)⟩

open Classical in

def idx (z : J → ℂ) : ℕ := Nat.find (exists_nzAt z)

open Classical in

def normPt (z : J → ℂ) : J → ℂ :=
  if h : idx z < Fintype.card J then (z ((Fintype.equivFin J).symm ⟨idx z, h⟩))⁻¹ • z else z

theorem nzAt_smul_iff {c : ℂ} (hc : c ≠ 0) (z : J → ℂ) (k : ℕ) : NZAt (c • z) k ↔ NZAt z k := by
  unfold NZAt
  refine forall_congr' fun h => ?_
  simp [Pi.smul_apply, smul_eq_mul, hc]

open Classical in
theorem idx_smul {c : ℂ} (hc : c ≠ 0) (z : J → ℂ) : idx (c • z) = idx z := by
  unfold idx
  refine le_antisymm (Nat.find_min' _ ((nzAt_smul_iff hc z _).2 (Nat.find_spec (exists_nzAt z))))
    (Nat.find_min' _ ((nzAt_smul_iff hc z _).1 (Nat.find_spec (exists_nzAt (c • z)))))

theorem normPt_smul {c : ℂ} (hc : c ≠ 0) (z : J → ℂ) : normPt (c • z) = normPt z := by
  classical
  have hi := idx_smul hc z
  unfold normPt
  rw [hi]
  split_ifs with h
  · rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv, mul_assoc, mul_left_comm, inv_mul_cancel₀ hc,
      mul_one]
  · have hz : z = 0 := by
      funext j
      by_contra hj
      apply h
      have hn : NZAt z (Fintype.equivFin J j) := fun hk => by simpa using hj
      exact lt_of_le_of_lt (Nat.find_min' _ hn) (Fintype.equivFin J j).2
    rw [hz, smul_zero]

theorem normPt_eq_smul (z : J → ℂ) : ∃ a : ℂ, a ≠ 0 ∧ normPt z = a • z := by
  classical
  unfold normPt
  split_ifs with h
  · refine ⟨_, inv_ne_zero ?_, rfl⟩
    have := Nat.find_spec (exists_nzAt z)
    exact this h
  · exact ⟨1, one_ne_zero, (one_smul ℂ z).symm⟩

theorem measurable_idx : Measurable (idx : (J → ℂ) → ℕ) := by
  classical
  refine measurable_find (fun z => exists_nzAt z) fun k => ?_
  by_cases hk : k < Fintype.card J
  · have : {z : J → ℂ | NZAt z k} = (fun z : J → ℂ => z ((Fintype.equivFin J).symm ⟨k, hk⟩)) ⁻¹' {0}ᶜ := by
      ext z
      simp [NZAt, hk]
    rw [this]
    exact (measurable_pi_apply _) (measurableSet_singleton 0).compl
  · have : {z : J → ℂ | NZAt z k} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact fun h => absurd h hk
    rw [this]
    exact MeasurableSet.univ

theorem measurable_normPt : Measurable (normPt : (J → ℂ) → J → ℂ) := by
  classical
  let G : (J → ℂ) × ℕ → J → ℂ := fun p =>
    if h : p.2 < Fintype.card J then (p.1 ((Fintype.equivFin J).symm ⟨p.2, h⟩))⁻¹ • p.1 else p.1
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun k => ?_
    by_cases hk : k < Fintype.card J
    · simp only [G, hk, dif_pos]
      exact ((measurable_pi_apply _).inv).smul measurable_id
    · simp only [G, hk, dif_neg, not_false_eq_true]
      exact measurable_id
  have : (normPt : (J → ℂ) → J → ℂ) = G ∘ fun z => (z, idx z) := by
    funext z
    rfl
  rw [this]
  exact hG.comp (measurable_id.prodMk measurable_idx)

theorem degZero_normPt {β : Type*} {g : (J → ℂ) → β} (hg : ∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z)
    (z : J → ℂ) : g (normPt z) = g z := by
  obtain ⟨a, ha, h⟩ := normPt_eq_smul z
  rw [h, hg a z ha]

end Normalise

section Conj

variable {J : Type} [Fintype J]

theorem conjPt_smul (c : ℂ) (z : J → ℂ) : conjPt (c • z) = starRingEnd ℂ c • conjPt z := by
  funext i
  simp [conjPt]

theorem conjPt_conjPt (z : J → ℂ) : conjPt (conjPt z) = z := by
  funext i
  simp [conjPt]

theorem conjPt_ne_zero {z : J → ℂ} (hz : z ≠ 0) : conjPt z ≠ 0 := fun h => hz (by
  rw [← conjPt_conjPt z, h]
  funext i
  simp [conjPt])

theorem eval_conjPt_map_int (z : J → ℂ) (f : MvPolynomial J ℤ) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [← secFun_map_int, secFun_conjPt, secFun_map_int]

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem conjPt_mem_pts {x : J → Ω} {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    conjPt z ∈ pts (coordIdeal ℤ x) :=
  ⟨conjPt_ne_zero hz.1, fun f hf => by rw [eval_conjPt_map_int, hz.2 f hf, map_zero]⟩

theorem measurableSet_pts (x : J → Ω) : MeasurableSet (pts (coordIdeal ℤ x)) := by
  have hcl : IsClosed {z : J → ℂ | ∀ g ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) g) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval _) continuous_const
  have : pts (coordIdeal ℤ x) = {0}ᶜ ∩ {z : J → ℂ | ∀ g ∈ coordIdeal ℤ x,
      eval z (map (Int.castRingHom ℂ) g) = 0} := by
    ext z
    simp [pts, conePts]
  rw [this]
  exact (measurableSet_singleton 0).compl.inter hcl.measurableSet

end Conj

section Resolution

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem sameOrbit_eq_smul {z z' : Ix κ → ℂ} (h : SameOrbit z z') : ∃ a : ℂ, a ≠ 0 ∧ z = a • z' := by
  obtain ⟨c, hc, hz⟩ := h
  refine ⟨c (), hc (), ?_⟩
  rw [hz]
  funext p
  rfl

theorem lift_mem_pts (d : HSMDatum D Ω κ) {y₀ y : d.R.X} (hy : y ∈ d.R.U y₀) :
    d.R.lift y₀ y ∈ pts (coordIdeal ℤ d.x) := by
  have hm := d.R.mem y₀ y hy
  refine ⟨fun h0 => ?_, hm.2⟩
  obtain ⟨i, hi⟩ := hm.1 ()
  exact hi (congrFun h0 _)

theorem resPt_mem_pts (d : HSMDatum D Ω κ) (y : d.R.X) : resPt d y ∈ pts (coordIdeal ℤ d.x) :=
  lift_mem_pts d (d.R.mem_U y)

theorem resPt_eq_smul_lift (d : HSMDatum D Ω κ) {y₀ y : d.R.X} (hy : y ∈ d.R.U y₀) :
    ∃ a : ℂ, a ≠ 0 ∧ resPt d y = a • d.R.lift y₀ y :=
  sameOrbit_eq_smul (d.R.compat y y₀ y ⟨d.R.mem_U y, hy⟩)

theorem continuousOn_lift (d : HSMDatum D Ω κ) (y₀ : d.R.X) :
    ContinuousOn (d.R.lift y₀) (d.R.U y₀) := by
  intro y hy
  refine (continuousAt_pi.2 fun p => ?_).continuousWithinAt
  obtain ⟨j, hj⟩ := d.R.A.cover y
  have hpt : d.R.A.chart j y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U y₀ :=
    ⟨(d.R.A.chart j).map_source hj, by simpa [(d.R.A.chart j).left_inv hj] using hy⟩
  have han := d.R.holo y₀ p j _ hpt
  have h2 : ContinuousAt ((fun y => d.R.lift y₀ y p) ∘ (d.R.A.chart j).symm ∘ d.R.A.chart j) y :=
    han.continuousAt.comp ((d.R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(d.R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(d.R.A.chart j).left_inv hy']

theorem continuous_degZero_resPt (d : HSMDatum D Ω κ) {β : Type*} [TopologicalSpace β]
    {g : (Ix κ → ℂ) → β} (hgc : ContinuousOn g {0}ᶜ) (hg : ∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) :
    Continuous fun y => g (resPt d y) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have hU := (d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)
  have h1 : ContinuousAt (d.R.lift y₀) y₀ := (continuousOn_lift d y₀).continuousAt hU
  have h0 : d.R.lift y₀ y₀ ∈ ({0}ᶜ : Set (Ix κ → ℂ)) := (lift_mem_pts d (d.R.mem_U y₀)).1
  have h2 : ContinuousAt (fun y => g (d.R.lift y₀ y)) y₀ :=
    (hgc.continuousAt (isOpen_compl_singleton.mem_nhds h0)).comp h1
  refine h2.congr ?_
  filter_upwards [hU] with y hy
  obtain ⟨a, ha, he⟩ := resPt_eq_smul_lift d hy
  rw [he, hg a _ ha]

theorem continuous_degZero_conj_resPt (d : HSMDatum D Ω κ) {β : Type*} [TopologicalSpace β]
    {g : (Ix κ → ℂ) → β} (hgc : ContinuousOn g {0}ᶜ) (hg : ∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) :
    Continuous fun y => g (conjPt (resPt d y)) := by
  refine continuous_degZero_resPt d (g := fun z => g (conjPt z)) ?_ fun c z hc => ?_
  · exact hgc.comp continuous_conjPt.continuousOn fun z hz => conjPt_ne_zero hz
  · rw [conjPt_smul, hg _ _ ((map_ne_zero _).2 hc)]

def symPt (d : HSMDatum D Ω κ) (y : d.R.X) : Ix κ → ℂ := normPt (resPt d y)

theorem symPt_mem_pts (d : HSMDatum D Ω κ) (y : d.R.X) : symPt d y ∈ pts (coordIdeal ℤ d.x) := by
  obtain ⟨a, ha, h⟩ := normPt_eq_smul (resPt d y)
  rw [symPt, h]
  exact smul_mem_pts_coord d.x (resPt_mem_pts d y) ha

theorem measurable_symPt (d : HSMDatum D Ω κ) : Measurable (symPt d) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y₀ : d.R.X => d.R.U y₀) d.R.isOpen_U
    fun y _ => Set.mem_iUnion.2 ⟨y, d.R.mem_U y⟩
  intro S hS
  have hloc : ∀ y₀ : d.R.X, MeasurableSet (d.R.U y₀ ∩ symPt d ⁻¹' S) := by
    intro y₀
    have hpw : Measurable ((d.R.U y₀).piecewise (d.R.lift y₀) (fun _ => 0)) :=
      (continuousOn_lift d y₀).measurable_piecewise continuousOn_const (d.R.isOpen_U y₀).measurableSet
    have he : d.R.U y₀ ∩ symPt d ⁻¹' S =
        d.R.U y₀ ∩ (d.R.U y₀).piecewise (d.R.lift y₀) (fun _ => 0) ⁻¹' (normPt ⁻¹' S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      refine and_congr_right fun hy => ?_
      rw [Set.piecewise_eq_of_mem _ _ _ hy, symPt]
      obtain ⟨a, ha, h⟩ := resPt_eq_smul_lift d hy
      rw [h, normPt_smul ha]
    rw [he]
    exact (d.R.isOpen_U y₀).measurableSet.inter (hpw (measurable_normPt hS))
  have : symPt d ⁻¹' S = ⋃ y₀ ∈ t, (d.R.U y₀ ∩ symPt d ⁻¹' S) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_and_left, exists_prop]
    constructor
    · intro hy
      obtain ⟨y₀, hy₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
      exact ⟨y₀, hy₀.2, hy₀.1, hy⟩
    · rintro ⟨y₀, -, -, hy⟩
      exact hy
  rw [this]
  exact Finset.measurableSet_biUnion t fun y₀ _ => hloc y₀

def symMeasure (d : HSMDatum D Ω κ) : Measure (Ix κ → ℂ) :=
  (2⁻¹ : ℝ≥0∞) • (d.dV.map (symPt d) + d.dV.map (conjPt ∘ symPt d))

instance isProbabilityMeasure_symMeasure (d : HSMDatum D Ω κ) : IsProbabilityMeasure (symMeasure d) := by
  have := d.vol.1
  have hm := measurable_symPt d
  have hc : Measurable (conjPt ∘ symPt d) := continuous_conjPt.measurable.comp hm
  constructor
  rw [symMeasure, Measure.smul_apply, Measure.add_apply, Measure.map_apply hm MeasurableSet.univ,
    Measure.map_apply hc MeasurableSet.univ, Set.preimage_univ, Set.preimage_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem symMeasure_compl_pts (d : HSMDatum D Ω κ) : symMeasure d (pts (coordIdeal ℤ d.x))ᶜ = 0 := by
  have hm := measurable_symPt d
  have hc : Measurable (conjPt ∘ symPt d) := continuous_conjPt.measurable.comp hm
  have hS := (measurableSet_pts d.x).compl
  rw [symMeasure, Measure.smul_apply, Measure.add_apply, Measure.map_apply hm hS, Measure.map_apply hc hS]
  have h1 : symPt d ⁻¹' (pts (coordIdeal ℤ d.x))ᶜ = ∅ := by
    ext y
    simp [symPt_mem_pts d y]
  have h2 : (conjPt ∘ symPt d) ⁻¹' (pts (coordIdeal ℤ d.x))ᶜ = ∅ := by
    ext y
    simp [conjPt_mem_pts (symPt_mem_pts d y)]
  rw [h1, h2, measure_empty, add_zero, smul_zero]

theorem map_conjPt_symMeasure (d : HSMDatum D Ω κ) : (symMeasure d).map conjPt = symMeasure d := by
  have hm := measurable_symPt d
  have hcj : Measurable (conjPt : (Ix κ → ℂ) → Ix κ → ℂ) := continuous_conjPt.measurable
  rw [symMeasure, Measure.map_smul, Measure.map_add _ _ hcj, Measure.map_map hcj hm,
    Measure.map_map hcj (hcj.comp hm)]
  have : conjPt ∘ (conjPt ∘ symPt d) = symPt d := by
    funext y
    exact conjPt_conjPt _
  rw [this, add_comm]

theorem integral_symMeasure (d : HSMDatum D Ω κ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {g : (Ix κ → ℂ) → E} (hgc : ContinuousOn g {0}ᶜ) (hg : ∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) :
    ∫ z, g z ∂(symMeasure d) =
      (2⁻¹ : ℝ) • ((∫ y, g (resPt d y) ∂d.dV) + ∫ y, g (conjPt (resPt d y)) ∂d.dV) := by
  have := d.vol.1
  have hm := measurable_symPt d
  have hc : Measurable (conjPt ∘ symPt d) := continuous_conjPt.measurable.comp hm
  have hgm : Measurable g := measurable_of_continuousOn_compl_singleton 0 hgc
  have e1 : (fun y => g (symPt d y)) = fun y => g (resPt d y) := by
    funext y
    exact degZero_normPt hg _
  have hgconj : ∀ (c : ℂ) z, c ≠ 0 → g (conjPt (c • z)) = g (conjPt z) := fun c z hc' => by
    rw [conjPt_smul, hg _ _ ((map_ne_zero _).2 hc')]
  have e2 : (fun y => g ((conjPt ∘ symPt d) y)) = fun y => g (conjPt (resPt d y)) := by
    funext y
    exact degZero_normPt (g := fun z => g (conjPt z)) hgconj _
  have hc1 := continuous_degZero_resPt d hgc hg
  have hc2 := continuous_degZero_conj_resPt d hgc hg
  have hi1 : Integrable (fun y => g (resPt d y)) d.dV :=
    integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
  have hi2 : Integrable (fun y => g (conjPt (resPt d y))) d.dV :=
    integrableOn_univ.1 (hc2.continuousOn.integrableOn_compact isCompact_univ)
  have hI1 : Integrable g (d.dV.map (symPt d)) := by
    rw [integrable_map_measure hgm.aestronglyMeasurable hm.aemeasurable]
    change Integrable (fun y => g (symPt d y)) d.dV
    rw [e1]; exact hi1
  have hI2 : Integrable g (d.dV.map (conjPt ∘ symPt d)) := by
    rw [integrable_map_measure hgm.aestronglyMeasurable hc.aemeasurable]
    change Integrable (fun y => g ((conjPt ∘ symPt d) y)) d.dV
    rw [e2]; exact hi2
  rw [symMeasure, integral_smul_measure, integral_add_measure hI1 hI2,
    integral_map hm.aemeasurable hgm.aestronglyMeasurable,
    integral_map hc.aemeasurable hgm.aestronglyMeasurable]
  simp only [e1]
  rw [e2, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

theorem dV_pos_of_isOpen (d : HSMDatum D Ω κ) {S : Set d.R.X} (hS : IsOpen S) (hne : S.Nonempty) :
    0 < d.dV S := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨j, hj⟩ := d.R.A.cover y
  obtain ⟨ν, hνc, hνp, hν⟩ := d.vol.2 j
  set S' := S ∩ (d.R.A.chart j).source with hS'
  have hS'o : IsOpen S' := hS.inter (d.R.A.chart j).open_source
  set T := (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' S' with hT
  have hTo : IsOpen T := (d.R.A.chart j).isOpen_inter_preimage_symm hS'o
  have hTy : d.R.A.chart j y ∈ T :=
    ⟨(d.R.A.chart j).map_source hj, by simp [(d.R.A.chart j).left_inv hj, hS', hy, hj]⟩
  have hvol : 0 < volume T := hTo.measure_pos volume ⟨_, hTy⟩
  have hmono : d.dV S' ≤ d.dV S := measure_mono Set.inter_subset_left
  refine lt_of_lt_of_le ?_ hmono
  rw [hν S' hS'o.measurableSet Set.inter_subset_right]
  have hae : AEMeasurable (fun w => ENNReal.ofReal (ν w)) (volume.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hνc.continuousOn.mono Set.inter_subset_left).aemeasurable hTo.measurableSet)
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [lintegral_eq_zero_iff' hae] at h0
  have h0' : ∀ᵐ w ∂(volume.restrict T), ENNReal.ofReal (ν w) = 0 := h0
  rw [ae_iff] at h0'
  have : volume.restrict T T = 0 := by
    refine measure_mono_null (fun w hw => ?_) h0'
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hνp w hw.1
  rw [Measure.restrict_apply_self] at this
  exact hvol.ne' this

end Resolution

end

end ResSym

end GroundTheory.Heights₂.Heights.HilbertSamuel
