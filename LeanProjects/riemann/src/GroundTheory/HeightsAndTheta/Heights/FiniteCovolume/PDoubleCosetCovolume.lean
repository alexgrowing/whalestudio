import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsDoubleCoset

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

section Setup

variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

def doubleCosetSetoid (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) : Setoid G₂ where
  r y y' := ∃ γ ∈ Γ, ∃ k ∈ K, y' = (Φ γ).2 * y * k
  iseqv :=
    { refl := fun y => ⟨1, Γ.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro y y' ⟨γ, hγ, k, hk, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
        simp [mul_assoc]
      trans := by
        rintro y y' y'' ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
        refine ⟨γ' * γ, Γ.mul_mem hγ' hγ, k * k', K.mul_mem hk hk', ?_⟩
        simp [mul_assoc] }

def leftCosetSet (K : Subgroup G₂) (s : G₂) : Set G₂ := {y | s⁻¹ * y ∈ K}

theorem isOpen_leftCosetSet {K : Subgroup G₂} (hK : IsOpen (K : Set G₂)) (s : G₂) :
    IsOpen (leftCosetSet K s) :=
  hK.preimage (continuous_const_mul s⁻¹)

theorem isCompact_leftCosetSet {K : Subgroup G₂} (hK : IsCompact (K : Set G₂)) (s : G₂) :
    IsCompact (leftCosetSet K s) := by
  have : leftCosetSet K s = (s * ·) '' (K : Set G₂) := by
    rw [Set.image_mul_left]; rfl
  rw [this]
  exact hK.image (continuous_const_mul s)

def sliceMeasure (Φ : G ≃ₜ* G₁ × G₂) (μ : Measure G) (V : Set G₂) : Measure G₁ :=
  (μ.restrict (Φ ⁻¹' (univ ×ˢ V))).map fun x => (Φ x).1

variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}

theorem measurable_fst_comp (Φ : G ≃ₜ* G₁ × G₂) : Measurable fun x => (Φ x).1 :=
  (continuous_fst.comp Φ.continuous).measurable

theorem measurableSet_preimage_univ_prod (hV : IsOpen V) : MeasurableSet (Φ ⁻¹' (univ ×ˢ V)) :=
  ((isOpen_univ.prod hV).preimage Φ.continuous).measurableSet

theorem preimage_prod_eq (A : Set G₁) :
    Φ ⁻¹' (A ×ˢ V) = (fun x => (Φ x).1) ⁻¹' A ∩ Φ ⁻¹' (univ ×ˢ V) := by
  ext x
  simp [mem_prod]

theorem measure_preimage_prod_eq_restrict (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) = μ.restrict (Φ ⁻¹' (univ ×ˢ V)) ((fun x => (Φ x).1) ⁻¹' A) := by
  rw [Measure.restrict_apply' (measurableSet_preimage_univ_prod hV), preimage_prod_eq]

theorem sliceMeasure_apply (hV : IsOpen V) {A : Set G₁} (hA : MeasurableSet A) :
    sliceMeasure Φ μ V A = μ (Φ ⁻¹' (A ×ˢ V)) := by
  rw [sliceMeasure, Measure.map_apply (measurable_fst_comp Φ) hA,
    measure_preimage_prod_eq_restrict hV]

theorem measure_preimage_prod_le (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) ≤ sliceMeasure Φ μ V A := by
  rw [measure_preimage_prod_eq_restrict hV]
  exact Measure.le_map_apply (measurable_fst_comp Φ).aemeasurable A

theorem sliceMeasure_isMulLeftInvariant [μ.IsMulLeftInvariant] (hV : IsOpen V) :
    (sliceMeasure Φ μ V).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).1 fun g A hA => ?_
  rw [sliceMeasure_apply hV (measurable_const_mul g hA), sliceMeasure_apply hV hA]
  have : Φ ⁻¹' (((g * ·) ⁻¹' A) ×ˢ V) =
      (fun x => Φ.symm (g, 1) * x) ⁻¹' (Φ ⁻¹' (A ×ˢ V)) := by
    ext x
    simp [mem_prod]
  rw [this, measure_preimage_mul]

theorem sliceMeasure_isFiniteMeasureOnCompacts [T2Space G₁] [IsFiniteMeasureOnCompacts μ]
    (hV : IsOpen V) (hVc : IsCompact V) : IsFiniteMeasureOnCompacts (sliceMeasure Φ μ V) := by
  refine ⟨fun A hA => ?_⟩
  rw [sliceMeasure_apply hV hA.isClosed.measurableSet]
  have : IsCompact (Φ ⁻¹' (A ×ˢ V)) :=
    (Homeomorph.isCompact_preimage Φ.toHomeomorph).2 (hA.prod hVc)
  exact this.measure_lt_top

variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]

theorem sliceMeasure_eq_smul_haar (hV : IsOpen V) (hVc : IsCompact V) :
    ∃ c : ℝ≥0, sliceMeasure Φ μ V = c • Measure.haar := by
  have := sliceMeasure_isMulLeftInvariant (Φ := Φ) (μ := μ) hV
  have := sliceMeasure_isFiniteMeasureOnCompacts (Φ := Φ) (μ := μ) hV hVc
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩

theorem quasiMeasurePreserving_fst_comp (hV : IsOpen V) (hVc : IsCompact V) :
    Measure.QuasiMeasurePreserving (fun x => (Φ x).1) (μ.restrict (Φ ⁻¹' (univ ×ˢ V)))
      (Measure.haar : Measure G₁) := by
  refine ⟨measurable_fst_comp Φ, fun A hA => ?_⟩
  change sliceMeasure Φ μ V A = 0
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, hA, smul_zero]

theorem measure_preimage_prod_null (hV : IsOpen V) (hVc : IsCompact V) {N : Set G₁}
    (hN : (Measure.haar : Measure G₁) N = 0) : μ (Φ ⁻¹' (N ×ˢ V)) = 0 := by
  rw [measure_preimage_prod_eq_restrict hV]
  exact (quasiMeasurePreserving_fst_comp hV hVc).preimage_null hN

theorem nullMeasurableSet_preimage_prod (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : NullMeasurableSet A (Measure.haar : Measure G₁)) :
    NullMeasurableSet (Φ ⁻¹' (A ×ˢ V)) μ := by
  rw [preimage_prod_eq]
  exact (nullMeasurableSet_restrict (measurableSet_preimage_univ_prod hV).nullMeasurableSet).1
    (hA.preimage (quasiMeasurePreserving_fst_comp hV hVc))

theorem measure_preimage_prod_lt_top (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : (Measure.haar : Measure G₁) A < ∞) : μ (Φ ⁻¹' (A ×ˢ V)) < ∞ := by
  refine (measure_preimage_prod_le hV A).trans_lt ?_
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hA

end Setup

theorem DoubleCosetCovolume.proof (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    DoubleCosetCovolume.Statement G G₁ G₂ := by
  intro Φ Γ _ K S hKc hKo hinj hcover hFD μ _
  classical
  let R := doubleCosetSetoid Φ Γ K

  let rep : Quotient R → G₂ := fun q =>
    if h : ∃ t ∈ S, Quotient.mk R t = q then h.choose else 1
  have rep_spec : ∀ t ∈ S, rep (Quotient.mk R t) ∈ S ∧
      Quotient.mk R (rep (Quotient.mk R t)) = Quotient.mk R t := by
    intro t ht
    have h : ∃ t' ∈ S, Quotient.mk R t' = Quotient.mk R t := ⟨t, ht, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let T : Finset (Quotient R) := S.image (Quotient.mk R)
  have hT : ∀ q ∈ T, rep q ∈ S ∧ Quotient.mk R (rep q) = q := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    exact rep_spec t ht

  let F : G₂ → Set G₁ := fun s =>
    if hs : s ∈ S then (hFD s hs (Measure.haar : Measure G₁)).choose else ∅
  have hF : ∀ s ∈ S, IsFundamentalDomain (sliceGroup Φ Γ K s) (F s) Measure.haar ∧
      (Measure.haar : Measure G₁) (F s) < ∞ := by
    intro s hs
    simp only [F, dif_pos hs]
    exact (hFD s hs Measure.haar).choose_spec
  have hVo := isOpen_leftCosetSet hKo
  have hVc := isCompact_leftCosetSet hKc
  let P : G₂ → Set G := fun s => Φ ⁻¹' (F s ×ˢ leftCosetSet K s)
  refine ⟨⋃ q ∈ T, P (rep q), IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_, ?_⟩
  ·
    refine NullMeasurableSet.biUnion T.countable_toSet fun q hq => ?_
    exact nullMeasurableSet_preimage_prod (hVo _) (hVc _) (hF _ (hT q hq).1).1.nullMeasurableSet
  ·
    let Nbad : G₂ → Set G₁ := fun s => {a | ¬ ∃ δ : sliceGroup Φ Γ K s, δ • a ∈ F s}
    let B : Set G := ⋃ η : Γ, ⋃ s ∈ S,
      (fun x => (η : G)⁻¹ * x) ⁻¹' (Φ ⁻¹' (Nbad s ×ˢ leftCosetSet K s))
    have hB : μ B = 0 := by
      refine measure_iUnion_null fun η => ?_
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      rw [measure_preimage_mul]
      exact measure_preimage_prod_null (hVo _) (hVc _) (ae_iff.1 (hF s hs).1.ae_covers)
    refine ae_iff.2 (measure_mono_null ?_ hB)
    intro x hx
    by_contra hxB
    apply hx
    obtain ⟨γ, hγ, t, ht, k, hk, hxt⟩ := hcover (Φ x).2
    have ht' : Quotient.mk R t = Quotient.mk R (Φ x).2 := Quotient.sound ⟨γ, hγ, k, hk, hxt⟩
    obtain ⟨hs, hsq⟩ := rep_spec t ht
    obtain ⟨η, hη, k', hk', hx2⟩ : R (rep (Quotient.mk R t)) (Φ x).2 :=
      Quotient.exact (hsq.trans ht')
    have e2 : (Φ ((η : G)⁻¹ * x)).2 = rep (Quotient.mk R t) * k' := by
      simp [hx2, mul_assoc]
    have hgood : ¬ (Φ ((η : G)⁻¹ * x)).1 ∈ Nbad (rep (Quotient.mk R t)) := by
      intro hbad
      apply hxB
      refine mem_iUnion.2 ⟨⟨η, hη⟩, mem_iUnion₂.2 ⟨_, hs, ?_⟩⟩
      refine ⟨hbad, ?_⟩
      show (rep (Quotient.mk R t))⁻¹ * (Φ ((η : G)⁻¹ * x)).2 ∈ K
      rw [e2, inv_mul_cancel_left]
      exact hk'
    simp only [Nbad, Set.mem_ofPred_eq, not_not] at hgood
    obtain ⟨δ, hδ⟩ := hgood
    obtain ⟨ζ, hζ, hζK, hζ1⟩ := mem_sliceGroup.1 δ.2
    refine ⟨⟨ζ * η⁻¹, Γ.mul_mem hζ (Γ.inv_mem hη)⟩, ?_⟩
    refine mem_iUnion₂.2 ⟨Quotient.mk R t, Finset.mem_image_of_mem _ ht, ?_⟩
    show Φ ((ζ * η⁻¹ : G) * x) ∈ F _ ×ˢ leftCosetSet K _
    rw [mul_assoc, map_mul]
    refine ⟨?_, ?_⟩
    · rw [Prod.fst_mul, hζ1]
      exact hδ
    · show (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (Φ ((η : G)⁻¹ * x)).2) ∈ K
      rw [e2]
      have : (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (rep (Quotient.mk R t) * k')) =
          (rep (Quotient.mk R t))⁻¹ * (Φ ζ).2 * rep (Quotient.mk R t) * k' := by
        simp only [mul_assoc]
      rw [this]
      exact K.mul_mem hζK hk'
  ·
    intro g hg
    let M : G₂ → Set G := fun s => ⋃ (h : (Φ g).1 ∈ sliceGroup Φ Γ K s),
      Φ ⁻¹' ((((⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) • F s) ∩ F s) ×ˢ leftCosetSet K s)
    have hM : μ (⋃ s ∈ S, M s) = 0 := by
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      refine measure_iUnion_null fun h => ?_
      refine measure_preimage_prod_null (hVo _) (hVc _) ?_
      have hne : (⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) ≠ 1 := by
        intro h1
        exact hg (Subtype.ext (hinj g g.2 (congrArg Subtype.val h1)))
      have := (hF s hs).1.aedisjoint hne
      simpa [Function.onFun, AEDisjoint] using this
    refine measure_mono_null ?_ hM
    rintro z ⟨hz1, hz2⟩
    rw [mem_smul_set_iff_inv_smul_mem] at hz1
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz1
    obtain ⟨q', hq', hzq'⟩ := mem_iUnion₂.1 hz2
    have hgz : Φ (g⁻¹ • z) = ((Φ g).1⁻¹ * (Φ z).1, (Φ g).2⁻¹ * (Φ z).2) := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul]
      simp [Prod.ext_iff]
    obtain ⟨hzF, hzK⟩ := hzq
    obtain ⟨hzF', hzK'⟩ := hzq'
    change (Φ (g⁻¹ • z)).1 ∈ F (rep q) at hzF
    change (Φ (g⁻¹ • z)).2 ∈ leftCosetSet K (rep q) at hzK
    rw [hgz] at hzF hzK
    simp only at hzF hzK
    change (rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2) ∈ K at hzK
    change (rep q')⁻¹ * (Φ z).2 ∈ K at hzK'
    have e1 : Quotient.mk R (rep q) = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨g, g.2, _, hzK, by group⟩
    have e2 : Quotient.mk R (rep q') = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨1, Γ.one_mem, _, hzK', by simp⟩
    have hqq : q = q' := by
      rw [← (hT q hq).2, ← (hT q' hq').2, e1, e2]
    subst hqq
    have hslice : (Φ g).1 ∈ sliceGroup Φ Γ K (rep q) := by
      refine mem_sliceGroup.2 ⟨g, g.2, ?_, rfl⟩
      have : (rep q)⁻¹ * (Φ g).2 * rep q =
          ((rep q)⁻¹ * (Φ z).2) * ((rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2))⁻¹ := by
        group
      rw [this]
      exact K.mul_mem hzK' (K.inv_mem hzK)
    refine mem_iUnion₂.2 ⟨rep q, (hT q hq).1, mem_iUnion.2 ⟨hslice, ?_⟩⟩
    refine ⟨⟨?_, hzF'⟩, hzK'⟩
    rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    exact hzF
  ·
    exact fun g => (measurePreserving_smul g μ).quasiMeasurePreserving
  ·
    refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.2 fun q hq => ?_)
    exact measure_preimage_prod_lt_top (hVo _) (hVc _) (hF _ (hT q hq).1).2

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
