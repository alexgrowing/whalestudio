import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

private theorem isIso_transitionMap_refl (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    IsIso (s.transitionMap h) := by
  have he : (homOfLE h : i ⟶ i).op = 𝟙 (Opposite.op i) := rfl
  have hid : s.transitionMap h = 𝟙 (s.schemeAt i) := by
    rw [SequenceOfBlowups.transitionMap_def, he]
    exact s.tower.map_id (Opposite.op i)
  rw [hid]
  infer_instance

theorem isIso_transitionMap_of_center_eq_top (s : SequenceOfBlowups X) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ s.length) (h : ∀ i, a ≤ i → i < b → s.center i = ⊤) :
    IsIso (s.transitionMap hab) := by
  revert hb h
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    exact isIso_transitionMap_refl s _
  | succ b hab ih =>
    intro hb h
    have hbl : b ≤ s.length := le_trans (Nat.le_succ b) hb
    have hlt : b < s.length := lt_of_lt_of_le (Nat.lt_succ_self b) hb
    have hcen : s.center b = ⊤ := h b hab (Nat.lt_succ_self b)
    have : IsIso (s.transitionMap hab) :=
      ih hbl fun i hi hib => h i hi (Nat.lt_succ_of_lt hib)
    have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc b) (s.center b) := s.isBlowupAlongIdealSheaf_blowupMorphism b hlt
    rw [hcen] at hB
    have : IsIso (s.transitionMap (Nat.le_succ b)) := by
      have h4 := hB.isIso_of_top
      rw [s.blowupMorphism_eq_transitionMap b] at h4
      exact h4
    have h3 : IsIso (s.transitionMap (Nat.le_succ b) ≫ s.transitionMap hab) := inferInstance
    rw [s.transitionMap_trans hab (Nat.le_succ b)] at h3
    exact h3

theorem exists_le_center_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    ∃ i, a ≤ i ∧ (s.center i ≠ ⊤ ∨ s.length ≤ i) :=
  ⟨max a s.length, le_max_left _ _, Or.inr (le_max_right _ _)⟩

noncomputable def nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

theorem nextNontrivialIndex_spec (s : SequenceOfBlowups X) (a : ℕ) :
    a ≤ s.nextNontrivialIndex a ∧ (s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)

theorem le_nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : a ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).1

theorem center_nextNontrivialIndex_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).2

theorem nextNontrivialIndex_le (s : SequenceOfBlowups X) {a i : ℕ} (hi : a ≤ i)
    (h : s.center i ≠ ⊤ ∨ s.length ≤ i) : s.nextNontrivialIndex a ≤ i :=
  @Nat.find_min' _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a) i ⟨hi, h⟩

theorem nextNontrivialIndex_le_length (s : SequenceOfBlowups X) {a : ℕ} (h : a ≤ s.length) :
    s.nextNontrivialIndex a ≤ s.length :=
  s.nextNontrivialIndex_le h (Or.inr le_rfl)

theorem center_eq_top_of_lt_nextNontrivialIndex (s : SequenceOfBlowups X) {a i : ℕ} (hai : a ≤ i)
    (h : i < s.nextNontrivialIndex a) : s.center i = ⊤ := by
  by_contra hc
  exact absurd (s.nextNontrivialIndex_le hai (Or.inl hc)) (not_le.mpr h)

noncomputable def nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (s.nextNontrivialIndex 0) (fun _ ih => s.nextNontrivialIndex (ih + 1)) j

@[simp] theorem nontrivialIndex_zero (s : SequenceOfBlowups X) : s.nontrivialIndex 0 = s.nextNontrivialIndex 0 := rfl

@[simp] theorem nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex (j + 1) = s.nextNontrivialIndex (s.nontrivialIndex j + 1) := rfl

theorem nontrivialIndex_lt_succ (s : SequenceOfBlowups X) (j : ℕ) : s.nontrivialIndex j < s.nontrivialIndex (j + 1) := by
  have h := s.le_nextNontrivialIndex (s.nontrivialIndex j + 1)
  rw [nontrivialIndex_succ]
  exact h

theorem succ_le_nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex j + 1 ≤ s.nontrivialIndex (j + 1) :=
  s.nontrivialIndex_lt_succ j

theorem nontrivialIndex_strictMono (s : SequenceOfBlowups X) : StrictMono s.nontrivialIndex :=
  strictMono_nat_of_lt_succ s.nontrivialIndex_lt_succ

theorem nontrivialIndex_monotone (s : SequenceOfBlowups X) : Monotone s.nontrivialIndex :=
  s.nontrivialIndex_strictMono.monotone

theorem le_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : j ≤ s.nontrivialIndex j :=
  s.nontrivialIndex_strictMono.le_apply

theorem center_nontrivialIndex_ne_top_or_length_le (s : SequenceOfBlowups X) (j : ℕ) :
    s.center (s.nontrivialIndex j) ≠ ⊤ ∨ s.length ≤ s.nontrivialIndex j := by
  cases j with
  | zero => exact s.center_nextNontrivialIndex_ne_top_or_length_le 0
  | succ j => exact s.center_nextNontrivialIndex_ne_top_or_length_le (s.nontrivialIndex j + 1)

theorem center_eq_top_of_lt_nontrivialIndex_zero (s : SequenceOfBlowups X) {i : ℕ} (h : i < s.nontrivialIndex 0) :
    s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex (Nat.zero_le i) h

theorem center_eq_top_of_nontrivialIndex_lt (s : SequenceOfBlowups X) {i j : ℕ} (h1 : s.nontrivialIndex j < i)
    (h2 : i < s.nontrivialIndex (j + 1)) : s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex h1 h2

theorem exists_length_le_nontrivialIndex (s : SequenceOfBlowups X) : ∃ j, s.length ≤ s.nontrivialIndex j :=
  ⟨s.length, s.le_nontrivialIndex s.length⟩

noncomputable def lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

theorem length_le_nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) :
    s.length ≤ s.nontrivialIndex s.lengthWithoutIsoBlowups :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex

private theorem nontrivialIndex_le_length_of_forall_lt (s : SequenceOfBlowups X) (j : ℕ)
    (h : ∀ i, i < j → s.nontrivialIndex i < s.length) : s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero =>
      show s.nextNontrivialIndex 0 ≤ s.length
      exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ j =>
      have hj : s.nontrivialIndex j < s.length := h j (Nat.lt_succ_self j)
      show s.nextNontrivialIndex (s.nontrivialIndex j + 1) ≤ s.length
      exact s.nextNontrivialIndex_le_length hj

theorem nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := by
  refine le_antisymm (nontrivialIndex_le_length_of_forall_lt s s.lengthWithoutIsoBlowups ?_)
    s.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  intro i hi
  have hmin := @Nat.find_min _ (fun _ => Classical.propDecidable _)
    s.exists_length_le_nontrivialIndex i hi
  exact not_le.mp hmin

theorem nontrivialIndex_lt_length (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j < s.length := by
  have h' : ¬ (s.length ≤ s.nontrivialIndex j) :=
    @Nat.find_min _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex j h
  exact not_le.mp h'

theorem nontrivialIndex_le_length (s : SequenceOfBlowups X) {j : ℕ} (h : j ≤ s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero => exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ i =>
    have hi : i < s.lengthWithoutIsoBlowups := lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hlt : s.nontrivialIndex i + 1 ≤ s.length := s.nontrivialIndex_lt_length hi
    exact s.nextNontrivialIndex_le_length hlt

theorem center_nontrivialIndex_ne_top (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.center (s.nontrivialIndex j) ≠ ⊤ := by
  rcases s.center_nontrivialIndex_ne_top_or_length_le j with hc | hc
  · exact hc
  · exact absurd hc (not_le.mpr (s.nontrivialIndex_lt_length h))

theorem isIso_transitionMap_nontrivialIndex_zero (s : SequenceOfBlowups X) :
    IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := by
  refine s.isIso_transitionMap_of_center_eq_top (Nat.zero_le (s.nontrivialIndex 0)) ?_ ?_
  · exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  · intro i _ hi
    exact s.center_eq_top_of_lt_nontrivialIndex_zero hi

theorem isIso_transitionMap_nontrivialIndex_succ (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ j)) := by
  refine s.isIso_transitionMap_of_center_eq_top (s.succ_le_nontrivialIndex_succ j)
    (s.nontrivialIndex_le_length (Nat.succ_le_of_lt h)) ?_
  intro i hi hib
  exact s.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hi) hib

noncomputable def objNontrivialIndexZeroIso (s : SequenceOfBlowups X) : s.schemeAt (s.nontrivialIndex 0) ≅ X :=
  haveI : IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := s.isIso_transitionMap_nontrivialIndex_zero
  (asIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0)))).trans s.isoZero

theorem objNontrivialIndexZeroIso_hom (s : SequenceOfBlowups X) :
    s.objNontrivialIndexZeroIso.hom = s.projectionToBase (s.nontrivialIndex 0) := by
  rw [projectionToBase_def]
  rfl

noncomputable def towerWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Monotone.functor s.nontrivialIndex_monotone).op ⋙ s.tower

private theorem isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map (s : SequenceOfBlowups X) (i : ℕ) (hi : i < s.lengthWithoutIsoBlowups) :
    Blowup.IsBlowupAlongIdealSheaf (s.towerWithoutIsoBlowups.map (homOfLE (Nat.le_succ i)).op) (s.center (s.nontrivialIndex i)) := by
  have : IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)) := s.isIso_transitionMap_nontrivialIndex_succ hi
  have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (s.nontrivialIndex i)) (s.center (s.nontrivialIndex i)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism (s.nontrivialIndex i) (s.nontrivialIndex_lt_length hi)
  have hcomp := hB.iso_hom_comp (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)))
  have heq : (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i))).hom ≫ s.transitionMapSucc (s.nontrivialIndex i)
      = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i)) := by
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
    exact s.transitionMap_trans (Nat.le_succ (s.nontrivialIndex i)) (s.succ_le_nontrivialIndex_succ i)
  rw [heq] at hcomp
  show Blowup.IsBlowupAlongIdealSheaf (s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i))) (s.center (s.nontrivialIndex i))
  exact hcomp

noncomputable def withoutIsoBlowups (s : SequenceOfBlowups X) : SequenceOfBlowups X where
  length := s.lengthWithoutIsoBlowups
  tower := s.towerWithoutIsoBlowups
  isoZero := s.objNontrivialIndexZeroIso
  center := fun j => s.center (s.nontrivialIndex j)
  isBlowup := s.isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map

@[simp] theorem withoutIsoBlowups_length (s : SequenceOfBlowups X) : s.withoutIsoBlowups.length = s.lengthWithoutIsoBlowups := rfl

@[simp] theorem withoutIsoBlowups_schemeAt (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.schemeAt j = s.schemeAt (s.nontrivialIndex j) := rfl

@[simp] theorem withoutIsoBlowups_center (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.center j = s.center (s.nontrivialIndex j) := rfl

theorem withoutIsoBlowups_isoObjZero (s : SequenceOfBlowups X) : s.withoutIsoBlowups.isoZero = s.objNontrivialIndexZeroIso := rfl

theorem withoutIsoBlowups_transitionMap (s : SequenceOfBlowups X) {j j' : ℕ} (h : j ≤ j') :
    s.withoutIsoBlowups.transitionMap h = s.transitionMap (s.nontrivialIndex_monotone h) := by
  rw [SequenceOfBlowups.transitionMap_def, SequenceOfBlowups.transitionMap_def]
  rfl

theorem withoutIsoBlowups_blowupMorphism (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.transitionMapSucc j = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ j)) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, withoutIsoBlowups_transitionMap]

theorem withoutIsoBlowups_center_ne_top (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.withoutIsoBlowups.length) :
    s.withoutIsoBlowups.center j ≠ ⊤ := by
  exact s.center_nontrivialIndex_ne_top h

theorem withoutIsoBlowups_lastObj (s : SequenceOfBlowups X) : s.withoutIsoBlowups.lastObj = s.lastObj :=
  congrArg s.schemeAt s.nontrivialIndex_lengthWithoutIsoBlowups

private theorem projectionToBase_eq_eqToHom_comp (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    s.projectionToBase a = eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b := by
  subst h
  simp

theorem withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase _

theorem withoutIsoBlowups_lastStructMap (s : SequenceOfBlowups X) :
    s.withoutIsoBlowups.lastStructMap = eqToHom s.withoutIsoBlowups_lastObj ≫ s.lastStructMap := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  have h1 : s.withoutIsoBlowups.lastStructMap = s.projectionToBase (s.nontrivialIndex s.withoutIsoBlowups.length) := by
    rw [lastStructMap_eq_projectionToBase, projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase _
  rw [h1, lastStructMap_eq_projectionToBase]
  exact projectionToBase_eq_eqToHom_comp s s.nontrivialIndex_lengthWithoutIsoBlowups

theorem withoutIsoBlowups_centersLieOver (s : SequenceOfBlowups X) {S : Set X} (h : s.CentersLieOver S) :
    s.withoutIsoBlowups.CentersLieOver S := by
  intro j hj x hx
  have hx' : x ∈ (s.center (s.nontrivialIndex j)).support := hx
  have h2 := h (s.nontrivialIndex j) (s.nontrivialIndex_lt_length hj) x hx'
  rw [withoutIsoBlowups_projectionToBase_eq_nontrivialIndex]
  exact h2

end SequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
