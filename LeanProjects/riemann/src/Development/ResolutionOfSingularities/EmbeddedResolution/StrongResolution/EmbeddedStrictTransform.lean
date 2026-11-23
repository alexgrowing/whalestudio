import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure AffineSpacePrincipalizationData (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] : Type (u + 1) where
  princ : PrincipalizationAlgorithm.{u}
  dim : ℕ
  emb : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin dim))
  emb_closedImmersion : AlgebraicGeometry.IsClosedImmersion emb
  emb_nonzeroOnComponents : NonzeroOnComponents (Scheme.Hom.ker emb)
  emb_comp : emb ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)) = pY
  ambient_smooth : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)))
  ambient_snc : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin dim))).IdealSheafData)

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

abbrev ambient : Scheme.{u} := affineSpaceIndexedBy k (ULift.{u} (Fin S.dim))

abbrev ambientToSpec : S.ambient ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedByToSpec k (ULift.{u} (Fin S.dim))

def principalizationSequence : IdealBlowupSequence S.ambientToSpec (Scheme.Hom.ker S.emb)
    ([] : List S.ambient.IdealSheafData) :=
  haveI := S.ambient_smooth
  S.princ k S.ambient S.ambientToSpec (Scheme.Hom.ker S.emb) S.emb_nonzeroOnComponents []
    S.ambient_snc

def ambientBlowups : SequenceOfBlowups S.ambient := S.principalizationSequence.toSequenceOfBlowups

abbrev ambientLength : ℕ := S.ambientBlowups.length

abbrev ambientLevel (i : ℕ) : Scheme.{u} := S.ambientBlowups.schemeAt i

abbrev ambientBlowupMorphism (i : ℕ) : S.ambientLevel (i + 1) ⟶ S.ambientLevel i := S.ambientBlowups.transitionMapSucc i

abbrev ambientCenter (i : ℕ) : (S.ambientLevel i).IdealSheafData := S.ambientBlowups.center i

def strictTransformIdeal (i : ℕ) : (S.ambientLevel i).IdealSheafData :=
  Nat.rec (motive := fun j => (S.ambientLevel j).IdealSheafData)
    (Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv))
    (fun j ih => Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) ih) i

@[simp] theorem strictTransformIdeal_zero :
    S.strictTransformIdeal 0 = Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv) := rfl

@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    S.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i) := rfl

abbrev strictTransform (i : ℕ) : Scheme.{u} := (S.strictTransformIdeal i).subscheme

abbrev strictTransformι (i : ℕ) : S.strictTransform i ⟶ S.ambientLevel i := (S.strictTransformIdeal i).subschemeι

theorem noetherianSpace_strictTransform (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.ambientLevel i)] :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
  Blowup.noetherianSpace_subscheme (S.strictTransformIdeal i)

theorem exists_strictTransformMap (i : ℕ) :
    ∃ f : S.strictTransform (i + 1) ⟶ S.strictTransform i,
      f ≫ S.strictTransformι i = S.strictTransformι (i + 1) ≫ S.ambientBlowupMorphism i := by
  have hle : S.strictTransformIdeal i ≤ (S.strictTransformIdeal (i + 1)).map (S.ambientBlowupMorphism i) := by
    refine le_trans (Scheme.IdealSheafData.le_map_comap (S.strictTransformIdeal i) (S.ambientBlowupMorphism i)) ?_
    exact Scheme.IdealSheafData.map_mono (S.ambientBlowupMorphism i)
      (Blowup.comap_le_strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i))
  exact ⟨(S.strictTransformIdeal (i + 1)).subschemeMap (S.strictTransformIdeal i) (S.ambientBlowupMorphism i) hle,
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ hle⟩

def strictTransformMap (i : ℕ) : S.strictTransform (i + 1) ⟶ S.strictTransform i := (S.exists_strictTransformMap i).choose

theorem strictTransformMap_comp_strictTransformι (i : ℕ) :
    S.strictTransformMap i ≫ S.strictTransformι i = S.strictTransformι (i + 1) ≫ S.ambientBlowupMorphism i :=
  (S.exists_strictTransformMap i).choose_spec

def discardedComponents (i : ℕ) : Set (Set ↥(S.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
    (S.strictTransformι i).base '' C ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))}

theorem mem_discardedComponents_iff (i : ℕ) (C : Set ↥(S.strictTransform i)) :
    C ∈ S.discardedComponents i ↔
      C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
        (S.strictTransformι i).base '' C ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)) := Iff.rfl

def discardedLocus (i : ℕ) : Set ↥(S.strictTransform i) := ⋃₀ (S.discardedComponents i)

theorem discardedLocus_eq_sUnion_discardedComponents (i : ℕ) : S.discardedLocus i = ⋃₀ (S.discardedComponents i) := rfl

theorem isClosed_discardedLocus (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)] :
    IsClosed (S.discardedLocus i) := by
  have hfin : (irreducibleComponents ↥(S.strictTransform i)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hsub : S.discardedComponents i ⊆ irreducibleComponents ↥(S.strictTransform i) := fun C hC =>
    ((S.mem_discardedComponents_iff i C).mp hC).1
  have hfin' : (S.discardedComponents i).Finite := Set.Finite.subset hfin hsub
  show IsClosed (⋃₀ (S.discardedComponents i))
  rw [Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion hfin'
    (fun C hC => isClosed_of_mem_irreducibleComponents C (hsub hC))

def discardedLocusClosure (i : ℕ) : TopologicalSpace.Closeds ↥(S.strictTransform i) :=
  ⟨closure (S.discardedLocus i), isClosed_closure⟩

theorem coe_discardedLocusClosure (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)] :
    (S.discardedLocusClosure i : Set ↥(S.strictTransform i)) = S.discardedLocus i := by
  show closure (S.discardedLocus i) = S.discardedLocus i
  exact (S.isClosed_discardedLocus i).closure_eq

def discardedIdeal (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (S.discardedLocusClosure i)

theorem discardedIdeal_eq_vanishingIdeal (i : ℕ) :
    S.discardedIdeal i = Scheme.IdealSheafData.vanishingIdeal (S.discardedLocusClosure i) := rfl

abbrev discardedSubscheme (i : ℕ) : Scheme.{u} := (S.discardedIdeal i).subscheme

abbrev discardedι (i : ℕ) : S.discardedSubscheme i ⟶ S.strictTransform i := (S.discardedIdeal i).subschemeι

def discardedLocusClosureCompl (i : ℕ) : (S.strictTransform i).Opens := (S.discardedLocusClosure i).compl

theorem coe_discardedLocusClosureCompl (i : ℕ) :
    ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      (S.discardedLocusClosure i : Set ↥(S.strictTransform i))ᶜ := rfl

def comapAmbientCenter (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  (S.ambientCenter i).comap (S.strictTransformι i)

theorem comapAmbientCenter_eq (i : ℕ) :
    S.comapAmbientCenter i = (S.ambientCenter i).comap (S.strictTransformι i) := rfl

def centerOffDetached (i : ℕ) : (S.strictTransform i).IdealSheafData :=
  Scheme.Hom.ker
    (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫ (S.discardedLocusClosureCompl i).ι)

theorem centerOffDetached_eq (i : ℕ) :
    S.centerOffDetached i =
      Scheme.Hom.ker
        (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
          (S.discardedLocusClosureCompl i).ι) := rfl

def discardedUnion (i : ℕ) : Scheme.{u} :=
  Nat.rec (motive := fun _ => Scheme.{u}) (⊥_ Scheme.{u})
    (fun j ih => ih ⨿ S.discardedSubscheme j) i

@[simp] theorem discardedUnion_zero : S.discardedUnion 0 = ⊥_ Scheme.{u} := rfl

@[simp] theorem discardedUnion_succ (i : ℕ) :
    S.discardedUnion (i + 1) = (S.discardedUnion i ⨿ S.discardedSubscheme i) := rfl

abbrev totalSpace (i : ℕ) : Scheme.{u} := S.strictTransform i ⨿ S.discardedUnion i

def transitionMap (i : ℕ) : S.totalSpace (i + 1) ⟶ S.totalSpace i :=
  coprod.desc (S.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : S.discardedUnion i ⟶ S.totalSpace i)
        (S.discardedι i ≫ coprod.inl) :
      S.discardedUnion i ⨿ S.discardedSubscheme i ⟶ S.totalSpace i)

theorem inl_comp_transitionMap (i : ℕ) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.transitionMap i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) := by
  exact coprod.inl_desc _ _

def centerOnTotalSpace (i : ℕ) : (S.totalSpace i).IdealSheafData :=
  Scheme.Hom.ker
    ((S.centerOffDetached i).subschemeι ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i))

theorem centerOnTotalSpace_eq_ker (i : ℕ) :
    S.centerOnTotalSpace i =
      Scheme.Hom.ker
        ((S.centerOffDetached i).subschemeι ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := rfl

private theorem exists_coprodInitialIso_inl_comp_eq_subschemeι {Z W : Scheme.{u}} (I : Z.IdealSheafData)
    (g : W ⟶ Z) (e0 : W ≅ I.subscheme) (he0 : e0.hom ≫ I.subschemeι = g) :
    ∃ e : (I.subscheme ⨿ (⊥_ Scheme.{u})) ≅ W,
      (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫ e.hom ≫ g =
        I.subschemeι := by
  refine ⟨(coprod.rightUnitor I.subscheme).trans e0.symm, ?_⟩
  have hunit : (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫
      (coprod.rightUnitor I.subscheme).hom = 𝟙 I.subscheme := coprod.inl_desc _ _
  have h1 : (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Scheme.{u})) ≫
      ((coprod.rightUnitor I.subscheme).trans e0.symm).hom = e0.inv := by
    rw [Iso.trans_hom, ← Category.assoc, hunit, Category.id_comp, Iso.symm_hom]
  rw [← Category.assoc, h1, ← he0, ← Category.assoc, e0.inv_hom_id, Category.id_comp]

private theorem exists_iso_ker_subscheme {W V : Scheme.{u}} (f : W ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion f] :
    ∃ e : W ≅ (Scheme.Hom.ker f).subscheme,
      e.hom ≫ (Scheme.Hom.ker f).subschemeι = f := by
  have hci2 : AlgebraicGeometry.IsClosedImmersion (Scheme.Hom.ker f).subschemeι := inferInstance
  have hk : Scheme.Hom.ker (Scheme.Hom.ker f).subschemeι = Scheme.Hom.ker f :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hα : AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker f).subschemeι f
      (le_of_eq hk) ≫ (Scheme.Hom.ker f).subschemeι = f :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hβ : AlgebraicGeometry.IsClosedImmersion.lift f (Scheme.Hom.ker f).subschemeι
      (le_of_eq hk.symm) ≫ f = (Scheme.Hom.ker f).subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hm1 : CategoryTheory.Mono f := inferInstance
  have hm2 : CategoryTheory.Mono (Scheme.Hom.ker f).subschemeι := inferInstance
  refine ⟨⟨AlgebraicGeometry.IsClosedImmersion.lift (Scheme.Hom.ker f).subschemeι f (le_of_eq hk),
      AlgebraicGeometry.IsClosedImmersion.lift f (Scheme.Hom.ker f).subschemeι (le_of_eq hk.symm),
      ?_, ?_⟩, hα⟩
  · rw [← cancel_mono f, Category.assoc, hβ, hα, Category.id_comp]
  · rw [← cancel_mono (Scheme.Hom.ker f).subschemeι, Category.assoc, hα, hβ, Category.id_comp]

theorem exists_totalSpaceZeroIso :
    ∃ e : S.totalSpace 0 ≅ Y,
      (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ e.hom ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformι 0 := by
  have := S.emb_closedImmersion
  have hci : AlgebraicGeometry.IsClosedImmersion (S.emb ≫ S.ambientBlowups.isoZero.inv) :=
    inferInstance
  obtain ⟨e0, he0⟩ := exists_iso_ker_subscheme (S.emb ≫ S.ambientBlowups.isoZero.inv)
  exact exists_coprodInitialIso_inl_comp_eq_subschemeι (Scheme.Hom.ker (S.emb ≫ S.ambientBlowups.isoZero.inv))
    (S.emb ≫ S.ambientBlowups.isoZero.inv) e0 he0

def totalSpaceZeroIso : S.totalSpace 0 ≅ Y := S.exists_totalSpaceZeroIso.choose

theorem totalSpaceZeroIso_spec :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
        (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformι 0 :=
  S.exists_totalSpaceZeroIso.choose_spec

def tower : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Functor.ofSequence (fun i => (S.transitionMap i).op)).leftOp

theorem tower_obj (i : ℕ) : S.tower.obj (Opposite.op i) = S.totalSpace i := rfl

theorem tower_map_succ (i : ℕ) :
    S.tower.map (homOfLE (Nat.le_succ i)).op = S.transitionMap i := by
  show ((Functor.ofSequence fun j => (S.transitionMap j).op).map (homOfLE (Nat.le_succ i))).unop
      = S.transitionMap i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < S.ambientLength → Blowup.IsBlowupAlongIdealSheaf (S.tower.map (homOfLE (Nat.le_succ i)).op) (S.centerOnTotalSpace i)

def blowupSequence (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := S.ambientLength
  tower := S.tower
  isoZero := S.totalSpaceZeroIso
  center := S.centerOnTotalSpace
  isBlowup := h

@[simp] theorem blowupSequence_length (h : S.TransitionsAreBlowups) : (S.blowupSequence h).length = S.ambientLength := rfl

@[simp] theorem blowupSequence_tower (h : S.TransitionsAreBlowups) : (S.blowupSequence h).tower = S.tower := rfl

theorem blowupSequence_isoObjZero (h : S.TransitionsAreBlowups) : (S.blowupSequence h).isoZero = S.totalSpaceZeroIso := rfl

@[simp] theorem blowupSequence_center (h : S.TransitionsAreBlowups) (i : ℕ) :
    (S.blowupSequence h).center i = S.centerOnTotalSpace i := rfl

def blowupSequenceWithoutIsos (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y := (S.blowupSequence h).withoutIsoBlowups

end AffineSpacePrincipalizationData

def AffineSpacePrincipalizationData.ofAffine (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    AffineSpacePrincipalizationData k Y pY where
  princ := A
  dim := (hemb k Y pY).choose
  emb := (hemb k Y pY).choose_spec.choose
  emb_closedImmersion := (hemb k Y pY).choose_spec.choose_spec.1
  emb_nonzeroOnComponents := (hemb k Y pY).choose_spec.choose_spec.2.1
  emb_comp := (hemb k Y pY).choose_spec.choose_spec.2.2
  ambient_smooth := hsm k ((hemb k Y pY).choose)
  ambient_snc := hsnc k ((hemb k Y pY).choose)

def EmbeddedPrincipalizationYieldsBlowups (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).TransitionsAreBlowups

def affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (h : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : AffineResolutionRule.{u} := by
  intro k _ _ Y pY _ _ _ _
  exact (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (h k Y pY)

end FunctorialResolution.EmbeddedResolution

end
