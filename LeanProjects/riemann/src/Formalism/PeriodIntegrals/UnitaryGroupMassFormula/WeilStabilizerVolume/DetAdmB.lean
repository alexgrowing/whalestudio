import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmA

noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Boxes

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}

def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))

variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}

theorem boxS_eq (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    boxS D = Set.pi univ fun c => {x : Af F | ∀ v, x v ∈ D c v} := by
  ext y
  simp [boxS]

theorem isCompact_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => isCompact_finite_adele_box (fun v => (hD.1 c v).2)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem isOpen_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsOpen (boxS D) := by
  rw [boxS_eq]
  exact isOpen_set_pi finite_univ fun c _ => isOpen_finite_adele_box (fun v => (hD.1 c v).1.isOpen)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem boxes_inter {s t : Set (ι → Af F)} (hs : s ∈ boxes F ι) (ht : t ∈ boxes F ι) :
    s ∩ t ∈ boxes F ι := by
  obtain ⟨D, hD, rfl⟩ := hs
  obtain ⟨D', hD', rfl⟩ := ht
  refine ⟨fun c v => D c v ∩ D' c v, ⟨fun c v => ⟨(hD.1 c v).1.inter (hD'.1 c v).1,
    (hD.1 c v).2.inter_right (hD'.1 c v).1.isClosed⟩, ?_⟩, ?_⟩
  · filter_upwards [hD.2, hD'.2] with v h1 h2 c
    rw [h1 c, h2 c, inter_self]
  · ext y
    simp only [boxS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ c v
      exact ⟨h1 c v, h2 c v⟩
    · intro h
      exact ⟨fun c v => (h c v).1, fun c v => (h c v).2⟩

theorem exists_box_mem (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  classical
  let D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun c v =>
    if y c v ∈ v.adicCompletionIntegers F then (v.adicCompletionIntegers F : Set (Fv F v))
    else (Homeomorph.subRight (y c v)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  refine ⟨D, ⟨fun c v => ?_, ?_⟩, fun c v => ?_⟩
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact ⟨isClopen_intV v, isCompact_intV v⟩
    · rw [show D c v = _ from if_neg h]
      exact ⟨isClopen_translate v _, isCompact_translate v _⟩
  · filter_upwards [eventually_all.2 fun c => (y c).eventually] with v hv c
    exact if_pos (hv c)
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact h
    · rw [show D c v = _ from if_neg h]
      exact mem_translate v _

theorem boxes_seq : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun s : {s // s ∈ boxes F ι} => (s.1 : Set (ι → Af F)))
    (fun s => by obtain ⟨D, hD, e⟩ := s.2; rw [e]; exact isOpen_boxS hD)
  have hU : ⋃ s ∈ T, (s.1 : Set (ι → Af F)) = univ := by
    rw [he]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact mem_iUnion.2 ⟨⟨boxS D, D, hD, rfl⟩, hy⟩
  have hne : T.Nonempty := by
    have h0 : (0 : ι → Af F) ∈ ⋃ s ∈ T, (s.1 : Set (ι → Af F)) := by
      rw [hU]
      trivial
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 h0
    exact ⟨s, hs⟩
  obtain ⟨g, hg⟩ := hT.exists_eq_range hne
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_⟩
  rw [← hU, hg]
  ext y
  simp

open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'

open Classical in
theorem upd_self (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) :
    upd D c v C c = Function.update (D c) v (D c v ∩ C) := if_pos rfl

open Classical in
theorem upd_ne (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) {c' : ι} (h : c' ≠ c) :
    upd D c v C c' = D c' := if_neg h

open Classical in
theorem mem_upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) (y : ι → Af F) :
    y ∈ boxS (upd D c v C) ↔ y ∈ boxS D ∧ y c v ∈ C := by
  classical
  constructor
  · intro hy
    refine ⟨fun c' w => ?_, ?_⟩
    · have h := hy c' w
      by_cases hc : c' = c
      · subst hc
        rw [upd_self] at h
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self] at h
          exact h.1
        · rw [Function.update_of_ne hw] at h
          exact h
      · rw [upd_ne D c v C hc] at h
        exact h
    · have h := hy c v
      rw [upd_self, Function.update_self] at h
      exact h.2
  · rintro ⟨hy, hC⟩ c' w
    by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨hy _ _, hC⟩
      · rw [Function.update_of_ne hw]
        exact hy _ _
    · rw [upd_ne D c v C hc]
      exact hy _ _

open Classical in
theorem isBoxD_upd {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (c : ι) (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)}
    (hC : IsClopen C ∧ IsCompact C) : IsBoxD (upd D c v C) := by
  classical
  refine ⟨fun c' w => ?_, ?_⟩
  · by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨(hD.1 _ _).1.inter hC.1, (hD.1 _ _).2.inter_right hC.1.isClosed⟩
      · rw [Function.update_of_ne hw]
        exact hD.1 _ _
    · rw [upd_ne D c v C hc]
      exact hD.1 _ _
  · filter_upwards [hD.2, eventually_cofinite_ne v] with w hw hwv c'
    by_cases hc : c' = c
    · subst hc
      rw [upd_self, Function.update_of_ne hwv]
      exact hw _
    · rw [upd_ne D c v C hc]
      exact hw c'

open Classical in
theorem pre_mem (c : ι) (v : HeightOneSpectrum (𝓞 F)) (W : Set (Fv F v)) (hW : IsOpen W) :
    MeasurableSet[generateFrom (boxes F ι)] ((fun y : ι → Af F => y c v) ⁻¹' W) := by
  classical
  let m' : MeasurableSpace (ι → Af F) := generateFrom (boxes F ι)
  obtain ⟨T, hT, hTc, rfl⟩ := open_eq_sUnion v hW
  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  choose Db hDb hbe using hbs
  have e : (fun y : ι → Af F => y c v) ⁻¹' ⋃₀ T = ⋃ C ∈ T, ⋃ n, boxS (upd (Db n) c v C) := by
    ext y
    simp only [mem_preimage, mem_sUnion, mem_iUnion, mem_upd, exists_prop]
    constructor
    · rintro ⟨C, hC, hy⟩
      have hy' : y ∈ ⋃ n, bs n := by
        rw [hbU]
        trivial
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy'
      exact ⟨C, hC, n, by rw [← hbe n]; exact hn, hy⟩
    · rintro ⟨C, hC, n, -, hy⟩
      exact ⟨C, hC, hy⟩
  rw [e]
  exact MeasurableSet.biUnion hT fun C hC => MeasurableSet.iUnion fun n =>
    measurableSet_generateFrom ⟨_, isBoxD_upd (hDb n) c v (hTc C hC), rfl⟩

theorem generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  classical
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    exact (isCompact_boxS hD).isClosed.measurableSet
  · intro s hs
    let Ev : (ι → Af F) → (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v) := fun y c v => y c v
    have hcont : Continuous Ev := continuous_pi fun c => continuous_pi fun v =>
      (RestrictedProduct.continuous_eval v).comp (continuous_apply c)
    have hinj : Function.Injective Ev := fun y y' h =>
      funext fun c => Subtype.ext (funext fun v => congrFun (congrFun h c) v)
    haveI : PolishSpace (ι → Af F) := TopoPolish.polish_of_lcsc _
    have hE := hcont.measurableEmbedding hinj
    have hc : ∀ c v, (borel (Fv F v)).comap (fun y : ι → Af F => y c v) ≤ generateFrom (boxes F ι) := by
      intro c v
      rw [borel, MeasurableSpace.comap_generateFrom]
      refine generateFrom_le ?_
      rintro _ ⟨W, hW, rfl⟩
      exact pre_mem c v W hW
    have hEv : (MeasurableSpace.pi : MeasurableSpace (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)).comap Ev
        ≤ generateFrom (boxes F ι) := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      exact iSup_le fun c => iSup_le fun v => hc c v
    rw [← hinj.preimage_image s]
    exact hEv _ ⟨_, hE.measurableSet_image.2 hs, rfl⟩

end Boxes

end PI.VolStabW.DeterminantAdmissible
