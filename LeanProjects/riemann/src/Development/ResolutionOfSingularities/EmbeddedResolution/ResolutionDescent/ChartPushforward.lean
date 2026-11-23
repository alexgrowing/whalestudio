import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def subschemeIsoOfEq {V : Scheme.{u}} {I J : V.IdealSheafData} (h : I = J) :
    I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg (fun K : V.IdealSheafData => K.subscheme) h)

@[reassoc (attr := simp)]
theorem subschemeIsoOfEq_hom_subschemeι {V : Scheme.{u}} {I J : V.IdealSheafData} (h : I = J) :
    (subschemeIsoOfEq h).hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp [subschemeIsoOfEq]

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

structure ChartPushforward (S S' : EmbeddedBlowupSequence k Y pY) where
  ambientMap : S.ambient ⟶ S'.ambient
  isClosedImmersion_ambientMap : AlgebraicGeometry.IsClosedImmersion ambientMap
  emb_ambientMap : S.emb ≫ ambientMap = S'.emb
  len_eq : S.length = S'.length
  levelMap : ∀ i : ℕ, i ≤ S'.length → (S.schemeAt i ⟶ S'.schemeAt i)
  isClosedImmersion_levelMap :
    ∀ (i : ℕ) (hi : i ≤ S'.length), AlgebraicGeometry.IsClosedImmersion (levelMap i hi)
  levelMap_zero :
    levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ ambientMap
  levelMap_blowdown :
    ∀ (i : ℕ) (hi : i < S'.length),
      levelMap (i + 1) hi ≫ S'.blowdown i = S.blowdown i ≫ levelMap i hi.le
  ambientCenter_eq :
    ∀ (i : ℕ) (hi : i < S'.length),
      S'.ambientCenter i = imageIdealSheaf (levelMap i hi.le) (S.ambientCenter i)
  ker_levelMap_succ :
    ∀ (i : ℕ) (hi : i < S'.length),
      (levelMap (i + 1) hi).ker =
        Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i) (levelMap i hi.le).ker

namespace ChartPushforward

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

instance instIsClosedImmersionAmbientMap (P : ChartPushforward S S') :
    AlgebraicGeometry.IsClosedImmersion P.ambientMap :=
  P.isClosedImmersion_ambientMap

instance instIsClosedImmersionLevelMap (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    AlgebraicGeometry.IsClosedImmersion (P.levelMap i hi) :=
  P.isClosedImmersion_levelMap i hi

theorem le_length (P : ChartPushforward S S') {i : ℕ} (hi : i ≤ S'.length) : i ≤ S.length :=
  hi.trans_eq P.len_eq.symm

end

section

variable (S S' : EmbeddedBlowupSequence k Y pY) (f : S.ambient ⟶ S'.ambient)
  [AlgebraicGeometry.IsClosedImmersion f]

private theorem isClosedImmersion_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i ≤ S'.length) :
    AlgebraicGeometry.IsClosedImmersion (h.2.choose i (hi.trans_eq h.1.symm)) :=
  h.2.choose_spec.1 i (hi.trans_eq h.1.symm)

private theorem isoObjZero_comm_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) :
    h.2.choose 0 ((Nat.zero_le S'.length).trans_eq h.1.symm) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ f := by
  exact h.2.choose_spec.2.1

private theorem blowdown_comm_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    h.2.choose (i + 1) (hi.trans_eq h.1.symm) ≫ S'.blowdown i =
      S.blowdown i ≫ h.2.choose i (hi.le.trans_eq h.1.symm) :=
  h.2.choose_spec.2.2.1 i (hi.trans_eq h.1.symm)

private theorem ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    S'.ambientCenter i =
      imageIdealSheaf (h.2.choose i (hi.le.trans_eq h.1.symm)) (S.ambientCenter i) :=
  h.2.choose_spec.2.2.2.1 i (hi.trans_eq h.1.symm)

private theorem ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) (i : ℕ) (hi : i < S'.length) :
    (h.2.choose (i + 1) (hi.trans_eq h.1.symm)).ker =
      Blowup.strictTransform (S'.blowdown i) (S'.ambientCenter i)
        (h.2.choose i (hi.le.trans_eq h.1.symm)).ker :=
  h.2.choose_spec.2.2.2.2 i (hi.trans_eq h.1.symm)

def ofIsPushforwardSeq (hemb : S.emb ≫ f = S'.emb)
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) : ChartPushforward S S' where
  ambientMap := f
  isClosedImmersion_ambientMap := inferInstance
  emb_ambientMap := hemb
  len_eq := h.1
  levelMap := fun i hi => h.2.choose i (hi.trans_eq h.1.symm)
  isClosedImmersion_levelMap := fun i hi => isClosedImmersion_of_isPushforwardBlowupSeq S S' f h i hi
  levelMap_zero := isoObjZero_comm_of_isPushforwardBlowupSeq S S' f h
  levelMap_blowdown := fun i hi => blowdown_comm_of_isPushforwardBlowupSeq S S' f h i hi
  ambientCenter_eq := fun i hi => ambientCenter_eq_imageIdealSheaf_of_isPushforwardBlowupSeq S S' f h i hi
  ker_levelMap_succ := fun i hi => ker_succ_eq_strictTransform_of_isPushforwardBlowupSeq S S' f h i hi

theorem ofIsPushforwardSeq_ambientMap (hemb : S.emb ≫ f = S'.emb)
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) :
    (ofIsPushforwardSeq S S' f hemb h).ambientMap = f := rfl

end

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

private theorem map_strictTransformIdeal_levelMap {T T' : EmbeddedBlowupSequence k Y pY}
    (P : ChartPushforward T T') (i : ℕ) :
    ∀ hi : i ≤ T'.length, (T.strictTransformIdeal i).map (P.levelMap i hi) = T'.strictTransformIdeal i := by
  induction i with
  | zero =>
    intro hi
    have key : T.ambientSeq.isoZero.inv ≫ P.levelMap 0 hi
        = P.ambientMap ≫ T'.ambientSeq.isoZero.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← P.levelMap_zero, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    have hcomp : (T.emb ≫ T.ambientSeq.isoZero.inv) ≫ P.levelMap 0 hi
        = T'.emb ≫ T'.ambientSeq.isoZero.inv := by
      rw [Category.assoc, key, ← Category.assoc, P.emb_ambientMap]
    rw [EmbeddedBlowupSequence.strictTransformIdeal_zero, EmbeddedBlowupSequence.strictTransformIdeal_zero, ← Scheme.Hom.ker_comp, hcomp]
  | succ n ih =>
    intro hi
    have hn : n < T'.length := Nat.lt_of_succ_le hi
    have : AlgebraicGeometry.IsNoetherian (T.schemeAt (n + 1)) :=
      T.isNoetherian_schemeAt (n + 1) (P.le_length hi)
    have : AlgebraicGeometry.IsNoetherian (T'.schemeAt (n + 1)) :=
      T'.isNoetherian_schemeAt (n + 1) hi
    have hsq : P.levelMap (n + 1) hi ≫ T'.blowdown n = T.blowdown n ≫ P.levelMap n hn.le :=
      P.levelMap_blowdown n hn
    have hcenter : (T.ambientCenter n).map (P.levelMap n hn.le) = T'.ambientCenter n := by
      rw [map_eq_ker_subschemeι_comp, P.ambientCenter_eq n hn, imageIdealSheaf_eq_ker]
    have hker : Scheme.Hom.ker (P.levelMap (n + 1) hi)
        = Blowup.strictTransform (T'.blowdown n) ((T.ambientCenter n).map (P.levelMap n hn.le))
            (Scheme.Hom.ker (P.levelMap n hn.le)) := by
      rw [hcenter]
      exact P.ker_levelMap_succ n hn
    have hmain := map_strictTransform_eq_strictTransform_map (P.levelMap n hn.le)
      (T.ambientCenter n) (T.strictTransformIdeal n) (T.blowdown n) (T'.blowdown n)
      (P.levelMap (n + 1) hi) hsq hker
    rw [EmbeddedBlowupSequence.strictTransformIdeal_succ, EmbeddedBlowupSequence.strictTransformIdeal_succ, hmain, ih hn.le, hcenter]

theorem exists_strictTransform_iso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    ∃ e : S.strictTransform i ≅ S'.strictTransform i,
      e.hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi := by
  have hmap := map_strictTransformIdeal_levelMap P i hi
  have hA : Scheme.Hom.ker (S.strictTransformι i) = S.strictTransformIdeal i := by
    rw [S.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have hA' : Scheme.Hom.ker (S'.strictTransformι i) = S'.strictTransformIdeal i := by
    rw [S'.strictTransformι_eq_subschemeι]
    exact Scheme.IdealSheafData.ker_subschemeι _
  have : AlgebraicGeometry.IsClosedImmersion (S.strictTransformι i ≫ P.levelMap i hi) := inferInstance
  have hker : Scheme.Hom.ker (S'.strictTransformι i) = Scheme.Hom.ker (S.strictTransformι i ≫ P.levelMap i hi) := by
    rw [Scheme.Hom.ker_comp, hA, hA', hmap]
  have := AlgebraicGeometry.IsClosedImmersion.isIso_lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) hker
  refine ⟨asIso (AlgebraicGeometry.IsClosedImmersion.lift (S'.strictTransformι i)
    (S.strictTransformι i ≫ P.levelMap i hi) (le_of_eq hker)), ?_⟩
  rw [asIso_hom, AlgebraicGeometry.IsClosedImmersion.lift_fac]

def strictTransformIso (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    S.strictTransform i ≅ S'.strictTransform i :=
  (P.exists_strictTransform_iso i hi).choose

@[reassoc (attr := simp)]
theorem strictTransformIso_hom_comp_strictTransformι (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    (P.strictTransformIso i hi).hom ≫ S'.strictTransformι i = S.strictTransformι i ≫ P.levelMap i hi :=
  (P.exists_strictTransform_iso i hi).choose_spec

@[reassoc]
theorem strictTransformIso_hom_comp_strictTransformMap (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (P.strictTransformIso (i + 1) hi).hom ≫ S'.strictTransformMap i =
      S.strictTransformMap i ≫ (P.strictTransformIso i hi.le).hom := by
  have hmono : Mono (S'.strictTransformι i) := by
    rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
    infer_instance
  rw [← cancel_mono (S'.strictTransformι i)]
  simp only [Category.assoc]
  rw [strictTransformIso_hom_comp_strictTransformι P i hi.le, EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S' i, ← Category.assoc,
    strictTransformIso_hom_comp_strictTransformι P (i + 1) hi, Category.assoc, P.levelMap_blowdown i hi,
    ← Category.assoc, ← EmbeddedBlowupSequence.strictTransformMap_comp_strictTransformι S i, Category.assoc]

theorem strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom (P : ChartPushforward S S') :
    (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom = S.strictTransformZeroIso.hom := by
  have key : ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
      = S.strictTransformZeroIso.hom ≫ S'.emb := by
    calc ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
        = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformZeroIso.hom ≫ S'.emb) := by
          rw [Category.assoc]
      _ = (P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ (S'.strictTransformι 0 ≫ S'.ambientSeq.isoZero.hom) := by
          rw [S'.strictTransformZeroIso_hom_emb]
      _ = ((P.strictTransformIso 0 (Nat.zero_le _)).hom ≫ S'.strictTransformι 0) ≫ S'.ambientSeq.isoZero.hom := by
          rw [Category.assoc]
      _ = (S.strictTransformι 0 ≫ P.levelMap 0 (Nat.zero_le _)) ≫ S'.ambientSeq.isoZero.hom := by
          rw [P.strictTransformIso_hom_comp_strictTransformι 0 (Nat.zero_le _)]
      _ = S.strictTransformι 0 ≫ (P.levelMap 0 (Nat.zero_le _) ≫ S'.ambientSeq.isoZero.hom) := by
          rw [Category.assoc]
      _ = S.strictTransformι 0 ≫ (S.ambientSeq.isoZero.hom ≫ P.ambientMap) := by
          rw [P.levelMap_zero]
      _ = (S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom) ≫ P.ambientMap := by
          rw [Category.assoc]
      _ = (S.strictTransformZeroIso.hom ≫ S.emb) ≫ P.ambientMap := by
          rw [S.strictTransformZeroIso_hom_emb]
      _ = S.strictTransformZeroIso.hom ≫ (S.emb ≫ P.ambientMap) := by
          rw [Category.assoc]
      _ = S.strictTransformZeroIso.hom ≫ S'.emb := by
          rw [P.emb_ambientMap]
  exact (cancel_mono S'.emb).mp key

private theorem range_subset_range_of_ker_le {U V W : Scheme.{u}} (f : U ⟶ W) (g : V ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g]
    (hle : Scheme.Hom.ker g ≤ Scheme.Hom.ker f) :
    Set.range ⇑f ⊆ Set.range ⇑g := by
  obtain ⟨e, he⟩ : ∃ e : U ⟶ V, e ≫ g = f :=
    ⟨AlgebraicGeometry.IsClosedImmersion.lift g f hle, by rw [IsClosedImmersion.lift_fac]⟩
  rintro y ⟨x, rfl⟩
  refine ⟨e.base x, ?_⟩
  have hx : ⇑(e ≫ g) x = ⇑f x := by rw [he]
  exact hx

private theorem support_ker_eq_range {U W : Scheme.{u}} (h : U ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion h] :
    ((Scheme.Hom.ker h).support : Set ↥W) = Set.range ⇑h := by
  have hker : Scheme.Hom.ker ((Scheme.Hom.ker h).subschemeι) = Scheme.Hom.ker h :=
    Scheme.IdealSheafData.ker_subschemeι _
  have h1 : Set.range ⇑((Scheme.Hom.ker h).subschemeι)
      = ((Scheme.Hom.ker h).support : Set ↥W) :=
    Scheme.IdealSheafData.range_subschemeι _
  rw [← h1]
  exact Set.Subset.antisymm (range_subset_range_of_ker_le _ h (le_of_eq hker.symm))
    (range_subset_range_of_ker_le h _ (le_of_eq hker))

theorem support_ambientCenter_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) =
      ⇑(P.levelMap i hi.le) '' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have hJ := P.ambientCenter_eq i hi
  rw [imageIdealSheaf_eq_ker] at hJ
  have hI : ((S.ambientCenter i).support : Set ↥(S.schemeAt i))
      = Set.range ⇑((S.ambientCenter i).subschemeι) := by
    have h2 := support_ker_eq_range ((S.ambientCenter i).subschemeι)
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h2
  have hcomp : ⇑((S.ambientCenter i).subschemeι ≫ P.levelMap i hi.le)
      = ⇑(P.levelMap i hi.le) ∘ ⇑((S.ambientCenter i).subschemeι) := rfl
  rw [hJ, support_ker_eq_range, hI, hcomp, Set.range_comp]

end

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
