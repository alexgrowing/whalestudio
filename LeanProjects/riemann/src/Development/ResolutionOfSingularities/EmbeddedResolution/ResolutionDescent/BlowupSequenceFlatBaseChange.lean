import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

@[simp]
theorem transitionMap_self_eq_id (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [s.transitionMap_def, show ((homOfLE h).op : op i ⟶ op i) = 𝟙 (op i) from rfl, s.tower.map_id]

instance instIsIsoStructMapZero (s : SequenceOfBlowups X) : IsIso (s.projectionToBase 0) := by
  rw [s.projectionToBase_zero]
  infer_instance

@[reassoc, simp]
theorem pullbackTransitionMap_comp_fst (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.fst φ (s.projectionToBase i) = pullback.fst φ (s.projectionToBase i') :=
  s.pullbackTransitionMap_fst φ h

@[reassoc, simp]
theorem pullbackTransitionMap_comp_snd (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i) =
      pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h :=
  s.pullbackTransitionMap_snd φ h

private theorem pullbackTransitionMap_refl (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    {a : ℕ} (h : a ≤ a) :
    s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase a)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self_eq_id, Category.comp_id, Category.id_comp]

private theorem pullbackTransitionMap_eq_comp (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    {a b c : ℕ} (hba : b ≤ a) (hcb : c ≤ b) (hca : c ≤ a) :
    s.pullbackTransitionMap φ hca = s.pullbackTransitionMap φ hba ≫ s.pullbackTransitionMap φ hcb := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [s.pullbackTransitionMap_snd, Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc,
      s.pullbackTransitionMap_snd, Category.assoc, s.transitionMap_trans]

def baseChangeTower (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) : ℕᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback φ (s.projectionToBase i.unop)
  map {_ _} f := s.pullbackTransitionMap φ (leOfHom f.unop)
  map_id i := pullbackTransitionMap_refl s φ (leOfHom (𝟙 i).unop)
  map_comp {_ _ _} f g :=
    pullbackTransitionMap_eq_comp s φ (leOfHom f.unop) (leOfHom g.unop) (leOfHom (f ≫ g).unop)

@[simp]
theorem baseChangeTower_obj (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) (i : ℕ) :
    (s.baseChangeTower φ).obj (op i) = pullback φ (s.projectionToBase i) := rfl

@[simp]
theorem baseChangeTower_map (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i i' : ℕ}
    (h : i ≤ i') :
    (s.baseChangeTower φ).map (homOfLE h).op = s.pullbackTransitionMap φ h := rfl

theorem isIso_pullback_fst_projectionToBase_zero (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    IsIso (pullback.fst φ (s.projectionToBase 0)) := by
  have hcomm : (𝟙 X') ≫ φ = (φ ≫ inv (s.projectionToBase 0)) ≫ s.projectionToBase 0 := by
    simp
  refine ⟨pullback.lift (𝟙 X') (φ ≫ inv (s.projectionToBase 0)) hcomm, ?_, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← Category.assoc,
        pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pullback.lift_fst]

instance instIsIsoPullbackFstStructMapZero (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    IsIso (pullback.fst φ (s.projectionToBase 0)) :=
  s.isIso_pullback_fst_projectionToBase_zero φ

def baseChangeTowerObjZeroIso (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    (s.baseChangeTower φ).obj (op 0) ≅ X' :=
  @asIso Scheme.{u} _ _ _ (pullback.fst φ (s.projectionToBase 0)) (s.isIso_pullback_fst_projectionToBase_zero φ)

@[simp]
theorem baseChangeTowerObjZeroIso_hom (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) :
    (s.baseChangeTowerObjZeroIso φ).hom = pullback.fst φ (s.projectionToBase 0) := rfl

theorem isPullback_pullbackTransitionMap (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) (i : ℕ) :
    IsPullback (pullback.snd φ (s.projectionToBase (i + 1))) (s.pullbackTransitionMap φ (Nat.le_succ i))
      (s.transitionMapSucc i) (pullback.snd φ (s.projectionToBase i)) := by
  have t : IsPullback (pullback.snd φ (s.projectionToBase i)) (pullback.fst φ (s.projectionToBase i))
      (s.projectionToBase i) φ := (IsPullback.of_hasPullback φ (s.projectionToBase i)).flip
  have hfst : s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.fst φ (s.projectionToBase i)
      = pullback.fst φ (s.projectionToBase (i + 1)) := s.pullbackTransitionMap_fst φ (Nat.le_succ i)
  have hstruct : s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
    rw [s.blowupMorphism_eq_transitionMap, s.transitionMap_comp_projectionToBase]
  have hsnd : pullback.snd φ (s.projectionToBase (i + 1)) ≫ s.transitionMapSucc i
      = s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.snd φ (s.projectionToBase i) := by
    rw [s.pullbackTransitionMap_snd, s.blowupMorphism_eq_transitionMap]
  have sq : IsPullback (pullback.snd φ (s.projectionToBase (i + 1)))
      (s.pullbackTransitionMap φ (Nat.le_succ i) ≫ pullback.fst φ (s.projectionToBase i))
      (s.transitionMapSucc i ≫ s.projectionToBase i) φ := by
    rw [hfst, hstruct]
    exact (IsPullback.of_hasPullback φ (s.projectionToBase (i + 1))).flip
  exact sq.of_bot hsnd t

private theorem isBlowupAlongIdealSheaf_baseChangeTower_map (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (i : ℕ) (hi : i < s.length) :
    Blowup.IsBlowupAlongIdealSheaf ((s.baseChangeTower φ).map (homOfLE (Nat.le_succ i)).op)
      ((s.center i).comap (pullback.snd φ (s.projectionToBase i))) :=
  (s.isBlowupAlongIdealSheaf_blowupMorphism i hi).of_isPullback_of_flat (pullback.snd φ (s.projectionToBase i))
    (s.isPullback_pullbackTransitionMap φ i)

def baseChange (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) [AlgebraicGeometry.Flat φ] :
    SequenceOfBlowups X' where
  length := s.length
  tower := s.baseChangeTower φ
  isoZero := s.baseChangeTowerObjZeroIso φ
  center i := (s.center i).comap (pullback.snd φ (s.projectionToBase i))
  isBlowup i hi := isBlowupAlongIdealSheaf_baseChangeTower_map s φ i hi

@[simp]
theorem baseChange_length (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] : (s.baseChange φ).length = s.length := rfl

@[simp]
theorem baseChange_schemeAt (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (i : ℕ) :
    (s.baseChange φ).schemeAt i = pullback φ (s.projectionToBase i) := rfl

@[simp]
theorem baseChange_blowupMorphism (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (i : ℕ) :
    (s.baseChange φ).transitionMapSucc i = s.pullbackTransitionMap φ (Nat.le_succ i) := rfl

@[simp]
theorem baseChange_isoObjZero_hom (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] :
    (s.baseChange φ).isoZero.hom = pullback.fst φ (s.projectionToBase 0) := rfl

@[simp]
theorem baseChange_center (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (i : ℕ) :
    (s.baseChange φ).center i = (s.center i).comap (pullback.snd φ (s.projectionToBase i)) := rfl

end SequenceOfBlowups

theorem isStrictPullbackSequenceOfBlowups_baseChange {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] : IsStrictPullbackBlowupSeq φ (s.baseChange φ) s := by
  refine ⟨rfl, fun i _ => pullback.snd φ (s.projectionToBase i), ?_, ?_, ?_⟩
  · show pullback.snd φ (s.projectionToBase 0) ≫ s.isoZero.hom
      = pullback.fst φ (s.projectionToBase 0) ≫ φ
    rw [← s.projectionToBase_zero, pullback.condition]
  · intro i _
    exact s.isPullback_pullbackTransitionMap φ i
  · intro i _
    rfl

end FunctorialResolution.EmbeddedResolution
