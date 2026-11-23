import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem baseChange_projectionToBase_eq_fst {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) [AlgebraicGeometry.Flat φ] (i : ℕ) :
    (s.baseChange φ).projectionToBase i = pullback.fst φ (s.projectionToBase i) := by
  induction i with
  | zero =>
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.baseChange_isoObjZero_hom]
  | succ n ih =>
    have hb : (s.baseChange φ).transitionMapSucc n ≫ (s.baseChange φ).projectionToBase n
        = (s.baseChange φ).projectionToBase (n + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase _ _
    rw [← hb, ih, SequenceOfBlowups.baseChange_blowupMorphism]
    exact SequenceOfBlowups.pullbackTransitionMap_comp_fst s φ _

structure SequenceOfBlowupsDescentDatum {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) where
  iso : ∀ i : ℕ, i ≤ t.length → (pullbackFstSchemeAt g t i ≅ pullbackSndSchemeAt g t i)
  comp_fst : ∀ (i : ℕ) (hi : i ≤ t.length),
    (iso i hi).hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase i)
      = pullback.fst (pullback.fst g g) (t.projectionToBase i)
  center_comap : ∀ (i : ℕ) (hi : i < t.length),
    ((t.center i).comap (pullback.snd (pullback.snd g g) (t.projectionToBase i))).comap
        (iso i hi.le).hom
      = (t.center i).comap (pullback.snd (pullback.fst g g) (t.projectionToBase i))
  comp_step : ∀ (i : ℕ) (hi : i < t.length),
    (iso (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ i)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ i) ≫ (iso i hi.le).hom

private structure DescendedSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) where
  X : Scheme.{u}
  str : X ⟶ Y
  gam : t.schemeAt n ⟶ X
  hsq : n ≤ t.length → IsPullback gam (t.projectionToBase n) str g
  hgam : ∀ hn : n ≤ t.length,
    (D.iso n hn).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ gam
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ gam

private structure DescendedBlowupOfSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) (P : DescendedSchemeData g t D n) where
  next : DescendedSchemeData g t D (n + 1)
  down : next.X ⟶ P.X
  cen : P.X.IdealSheafData
  hblow : n < t.length → Blowup.IsBlowupAlongIdealSheaf down cen
  hpb : n < t.length → IsPullback next.gam (t.transitionMapSucc n) down P.gam
  hcen : n < t.length → t.center n = cen.comap P.gam

private def descendedSchemeDataZero {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : DescendedSchemeData g t D 0 where
  X := Y
  str := 𝟙 Y
  gam := t.projectionToBase 0 ≫ g
  hsq := fun _ => (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  hgam := fun h0 => by
    have c1 : pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g
        = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c2 : pullback.fst (pullback.snd g g) (t.projectionToBase 0) ≫ pullback.snd g g
        = pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c3 : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
    have hf := D.comp_fst 0 h0
    calc (D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
          (t.projectionToBase 0 ≫ g)
        = ((D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
            t.projectionToBase 0) ≫ g := by
          simp only [Category.assoc]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.snd g g) ≫ g := by
          rw [← c2, ← Category.assoc, hf]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g) ≫ g := by
          rw [Category.assoc, Category.assoc, c3]
      _ = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ (t.projectionToBase 0 ≫ g) := by
          rw [c1, Category.assoc]

private def descendedBlowupAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) (P : DescendedSchemeData g t D n) : DescendedBlowupOfSchemeData g t D n P :=
  if hn : n < t.length then
    let S := descendedBlowupData g t hn P.str P.gam (P.hsq hn.le) (D.iso n hn.le)
      (D.iso (n + 1) (Nat.succ_le_of_lt hn)) (D.comp_step n hn) (D.center_comap n hn)
      (D.comp_fst n hn.le) (P.hgam hn.le)
    { next :=
        { X := S.total
          str := S.totalStruct
          gam := S.totalComparison
          hsq := fun _ => S.isPullback_base
          hgam := fun _ => S.hom_comparison }
      down := S.down
      cen := S.totalCenter
      hblow := fun _ => S.isBlowup_down
      hpb := fun _ => S.isPullback_sq
      hcen := fun _ => S.center_comap.symm }
  else
    { next :=
        { X := t.schemeAt (n + 1)
          str := t.projectionToBase (n + 1) ≫ g
          gam := 𝟙 (t.schemeAt (n + 1))
          hsq := fun hle => absurd (Nat.lt_of_succ_le hle) hn
          hgam := fun hle => absurd (Nat.lt_of_succ_le hle) hn }
      down := t.transitionMapSucc n ≫ P.gam
      cen := ⊤
      hblow := fun hlt => absurd hlt hn
      hpb := fun hlt => absurd hlt hn
      hcen := fun hlt => absurd hlt hn }

private def descendedSchemeDataAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : DescendedSchemeData g t D n :=
  Nat.rec (motive := fun m => DescendedSchemeData g t D m) (descendedSchemeDataZero g t D)
    (fun m P => (descendedBlowupAt g t D m P).next) n

private def descendedSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : Scheme.{u} :=
  (descendedSchemeDataAt g t D n).X

private def descendedBlowupMorphism {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : descendedSchemeAt g t D (n + 1) ⟶ descendedSchemeAt g t D n :=
  (descendedBlowupAt g t D n (descendedSchemeDataAt g t D n)).down

private def descendedTower {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    ℕᵒᵖ ⥤ Scheme.{u} :=
  Functor.ofOpSequence (descendedBlowupMorphism g t D)

private def descendedSequenceOfBlowups {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    SequenceOfBlowups Y where
  length := t.length
  tower := descendedTower g t D
  isoZero := Iso.refl Y
  center := fun i => (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).cen
  isBlowup := fun i hi => by
    have hmap : (descendedTower g t D).map (homOfLE (Nat.le_succ i)).op = descendedBlowupMorphism g t D i :=
      Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
    rw [hmap]
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hblow hi

private theorem exists_isStrictPullbackSequenceOfBlowups_of_descentDatum {W Y : Scheme.{u}} (g : W ⟶ Y)
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  refine ⟨descendedSequenceOfBlowups g t D, rfl, fun i _ => (descendedSchemeDataAt g t D i).gam, ?_, ?_, ?_⟩
  · show (descendedSchemeDataAt g t D 0).gam ≫ (descendedSequenceOfBlowups g t D).isoZero.hom = t.isoZero.hom ≫ g
    have h0 : (descendedSchemeDataAt g t D 0).gam = t.projectionToBase 0 ≫ g := rfl
    rw [h0, SequenceOfBlowups.projectionToBase_zero]
    exact Category.comp_id _
  · intro i hi
    have hmap : (descendedSequenceOfBlowups g t D).transitionMapSucc i = descendedBlowupMorphism g t D i := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_def]
      exact Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
    rw [hmap]
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hpb hi
  · intro i hi
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hcen hi

theorem exists_isStrictPullback_of_isomorphic_baseChange {W Y : Scheme.{u}}
    (g : W ⟶ Y) [AlgebraicGeometry.Flat g] [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W)
    (h : (t.baseChange (pullback.fst g g)).Isomorphic (t.baseChange (pullback.snd g g))) :
    ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  obtain ⟨-, e, hzero, hstep, hcen⟩ := h
  have hlp : (t.baseChange (pullback.fst g g)).length = t.length :=
    t.baseChange_length (pullback.fst g g)
  refine exists_isStrictPullbackSequenceOfBlowups_of_descentDatum g t
    { iso := fun i hi => e i (by rw [hlp]; exact hi)
      comp_fst := ?_
      center_comap := ?_
      comp_step := ?_ }
  · intro i hi
    have key := SequenceOfBlowups.iso_hom_comp_projectionToBase (t.baseChange (pullback.fst g g))
      (t.baseChange (pullback.snd g g)) _ e hstep hzero i (by rw [hlp]; exact hi)
    rw [baseChange_projectionToBase_eq_fst, baseChange_projectionToBase_eq_fst] at key
    exact key
  · intro i hi
    have key := hcen i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_center, SequenceOfBlowups.baseChange_center] at key
    exact key
  · intro i hi
    have key := hstep i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_blowupMorphism] at key
    exact key

end FunctorialResolution.EmbeddedResolution
