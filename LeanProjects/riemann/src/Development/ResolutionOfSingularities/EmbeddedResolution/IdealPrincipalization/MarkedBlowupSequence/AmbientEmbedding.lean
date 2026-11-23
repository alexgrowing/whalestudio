import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def BlowupPreservesNoetherian : Prop :=
  ∀ (X X' : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z → AlgebraicGeometry.IsNoetherian X'

structure AmbientEmbedding {S : Scheme.{u}} (s : BlowupSequenceData S) (n : ℕ) : Type (u + 1) where
  ambient : Scheme.{u}
  emb : s.obj n ⟶ ambient
  emb_isClosedImmersion : AlgebraicGeometry.IsClosedImmersion emb
  isNoetherian_ambient_of_le_length : n ≤ s.length → AlgebraicGeometry.IsNoetherian ambient

private theorem isClosedImmersion_isoObjZero_hom_comp {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (s : BlowupSequenceData S) :
    AlgebraicGeometry.IsClosedImmersion (s.isoZero.hom ≫ ι) := by
  have : AlgebraicGeometry.IsClosedImmersion s.isoZero.hom := inferInstance
  infer_instance

private theorem isNoetherian_blowup_of_isNoetherian (hno : BlowupPreservesNoetherian.{u})
    {A : Scheme.{u}} (hA : AlgebraicGeometry.IsNoetherian A) (Z : A.IdealSheafData) :
    AlgebraicGeometry.IsNoetherian (Blowup.blowup Z) := by
  have := hA
  exact hno A (Blowup.blowup Z) (Blowup.blowup.proj Z) Z (Blowup.blowup.isBlowupAlongIdealSheaf_proj Z)

private theorem comap_imageIdealSheaf_of_isClosedImmersion {S' A : Scheme.{u}} (σ : S' ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion σ] (J : S'.IdealSheafData) :
    (imageIdealSheaf σ J).comap σ = J := by
  have h : imageIdealSheaf σ J = J.map σ := rfl
  rw [h]
  exact Blowup.comap_map_of_isClosedImmersion σ J

private theorem preimage_support_subset_support_comap {S' A : Scheme.{u}} (σ : S' ⟶ A) (Z : A.IdealSheafData) :
    σ.base ⁻¹' (Z.support : Set ↥A) ⊆ ((Z.comap σ).support : Set ↥S') := by
  simp [Scheme.IdealSheafData.support_comap]

private theorem exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    {S' A : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian A] (σ : S' ⟶ A)
    [AlgebraicGeometry.IsClosedImmersion σ] (J : S'.IdealSheafData) {S'' : Scheme.{u}}
    (f : S'' ⟶ S') (hf : Blowup.IsBlowupAlongIdealSheaf f J)
    (hc : ∀ T ∈ irreducibleComponents ↥S', ¬ T ⊆ (J.support : Set ↥S')) :
    ∃ τ : S'' ⟶ Blowup.blowup (imageIdealSheaf σ J),
      AlgebraicGeometry.IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ J) = f ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker := by
  have hπ : Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) :=
    Blowup.blowup.isBlowupAlongIdealSheaf_proj _
  have hcomap : (imageIdealSheaf σ J).comap σ = J := comap_imageIdealSheaf_of_isClosedImmersion σ J
  have hsupp : ∀ T ∈ irreducibleComponents ↥S',
      ¬ (σ.base '' T) ⊆ ((imageIdealSheaf σ J).support : Set ↥A) := by
    intro T hT hsub
    refine hc T hT ?_
    have h2 := (Set.image_subset_iff.mp hsub).trans (preimage_support_subset_support_comap σ (imageIdealSheaf σ J))
    rwa [hcomap] at h2
  obtain ⟨ψ, hψ1, hψ2⟩ := hres A (Blowup.blowup (imageIdealSheaf σ J)) S' σ
    (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) hπ hsupp
  rw [hcomap] at hψ2
  have hab : hψ2.lift f hf.1 ≫ ψ = f := hψ2.lift_comp f hf.1
  have hba : hf.lift ψ hψ2.1 ≫ f = ψ := hf.lift_comp ψ hψ2.1
  have hid1 : hψ2.lift f hf.1 ≫ hf.lift ψ hψ2.1 = 𝟙 S'' := by
    refine hf.hom_ext hf.1 ?_ (Category.id_comp f)
    rw [Category.assoc, hba, hab]
  have hid2 : hf.lift ψ hψ2.1 ≫ hψ2.lift f hf.1 = 𝟙 _ := by
    refine hψ2.hom_ext hψ2.1 ?_ (Category.id_comp ψ)
    rw [Category.assoc, hab, hba]
  have : IsIso (hψ2.lift f hf.1) := ⟨⟨hf.lift ψ hψ2.1, hid1, hid2⟩⟩
  refine ⟨hψ2.lift f hf.1 ≫
      (Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ J)) (imageIdealSheaf σ J) σ.ker).subschemeι,
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hψ1, ← Category.assoc, hab]
  · rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_subschemeι _

private theorem exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (_hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    ∃ τ : s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)),
      AlgebraicGeometry.IsClosedImmersion τ ∧
      τ ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) = s.map n ≫ σ ∧
      τ.ker = Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
          (imageIdealSheaf σ (s.center n)) σ.ker := by
  have := hσ
  have := hA
  have : AlgebraicGeometry.IsLocallyNoetherian A := inferInstance
  exact exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf hres σ (s.center n) (s.map n) (s.isBlowup n hn) hc

private def embeddingIntoAmbientBlowup (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ (s.center n)) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose

private theorem isClosedImmersion_embeddingIntoBlowupImageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.1

private theorem embeddingIntoBlowupImageIdealSheaf_comp_proj (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc ≫ Blowup.blowup.proj (imageIdealSheaf σ (s.center n)) =
      s.map n ≫ σ :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.2.1

private theorem ker_embeddingIntoBlowupImageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Scheme.{u}) (σ : s.obj n ⟶ A)
    (hσ : AlgebraicGeometry.IsClosedImmersion σ) (hA : AlgebraicGeometry.IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : Set ↥(s.obj n))) :
    (embeddingIntoAmbientBlowup hres hno s n hn A σ hσ hA hc).ker =
      Blowup.strictTransform (Blowup.blowup.proj (imageIdealSheaf σ (s.center n)))
        (imageIdealSheaf σ (s.center n)) σ.ker :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hσ hA hc).choose_spec.2.2

private def ambientEmbeddingZero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) : AmbientEmbedding s 0 where
  ambient := X
  emb := s.isoZero.hom ≫ ι
  emb_isClosedImmersion := isClosedImmersion_isoObjZero_hom_comp ι s
  isNoetherian_ambient_of_le_length := fun _ => inferInstance

private def ambientEmbeddingSucc (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) :
    Σ t : AmbientEmbedding s (n + 1), (t.ambient ⟶ st.ambient) :=
  if h : n < s.length then
    ⟨{ ambient := Blowup.blowup (imageIdealSheaf st.emb (s.center n))
       emb := embeddingIntoAmbientBlowup hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
         (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       emb_isClosedImmersion := isClosedImmersion_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb
         st.emb_isClosedImmersion (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
       isNoetherian_ambient_of_le_length := fun _ =>
         isNoetherian_blowup_of_isNoetherian hno (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h))
           (imageIdealSheaf st.emb (s.center n)) },
     Blowup.blowup.proj (imageIdealSheaf st.emb (s.center n))⟩
  else
    ⟨{ ambient := s.obj (n + 1)
       emb := 𝟙 (s.obj (n + 1))
       emb_isClosedImmersion := inferInstance
       isNoetherian_ambient_of_le_length := fun hle => absurd (Nat.lt_of_succ_le hle) h },
     s.map n ≫ st.emb⟩

private theorem isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) (h : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSucc hres hno s hcen n st).2 (imageIdealSheaf st.emb (s.center n)) := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj _

private theorem succAmbientEmbedding_comp_blowupMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb ≫ (ambientEmbeddingSucc hres hno s hcen n st).2 =
      s.map n ≫ st.emb := by
  unfold ambientEmbeddingSucc
  by_cases h : n < s.length
  · rw [dif_pos h]
    exact embeddingIntoBlowupImageIdealSheaf_comp_proj hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
      (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)
  · rw [dif_neg h]
    exact Category.id_comp _

private theorem ker_succAmbientEmbedding_eq_strictTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) {S : Scheme.{u}} (s : BlowupSequenceData S)
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i)))
    (n : ℕ) (st : AmbientEmbedding s n) (h : n < s.length) :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb.ker =
      Blowup.strictTransform (ambientEmbeddingSucc hres hno s hcen n st).2
        (imageIdealSheaf st.emb (s.center n)) st.emb.ker := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact ker_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
    (st.isNoetherian_ambient_of_le_length (Nat.le_of_lt h)) (hcen n h)

private def ambientEmbedding {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    ∀ n : ℕ, AmbientEmbedding s n := fun n =>
  Nat.rec (motive := fun n => AmbientEmbedding s n) (ambientEmbeddingZero ι s)
    (fun m st => (ambientEmbeddingSucc hres hno s hcen m st).1) n

private def ambientEmbeddingSuccMap {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientEmbedding ι s hres hno hcen (n + 1)).ambient ⟶ (ambientEmbedding ι s hres hno hcen n).ambient :=
  (ambientEmbeddingSucc hres hno s hcen n (ambientEmbedding ι s hres hno hcen n)).2

private theorem isBlowupAlongIdealSheaf_ambientBlowupMorphism {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSuccMap ι s hres hno hcen n)
      (imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb (s.center n)) :=
  isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

def ambientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) : BlowupSequenceData X where
  length := s.length
  obj := fun n => (ambientEmbedding ι s hres hno hcen n).ambient
  map := fun n => ambientEmbeddingSuccMap ι s hres hno hcen n
  isoZero := Iso.refl X
  center := fun n => imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb (s.center n)
  isBlowup := fun n hn => isBlowupAlongIdealSheaf_ambientBlowupMorphism ι s hres hno hcen n hn

def embeddingIntoAmbientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    s.obj n ⟶ (ambientBlowupSequence ι s hres hno hcen).obj n :=
  (ambientEmbedding ι s hres hno hcen n).emb

@[simp]
theorem ambientBlowupSequence_length {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).length = s.length := rfl

theorem ambientBlowupSequence_schemeAt_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).obj 0 = X := rfl

theorem ambientBlowupSequence_isoObjZero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    (ambientBlowupSequence ι s hres hno hcen).isoZero = Iso.refl X := rfl

@[simp]
theorem ambientBlowupSequence_center {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    (ambientBlowupSequence ι s hres hno hcen).center n =
      imageIdealSheaf (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) (s.center n) := rfl

theorem isNoetherian_ambientBlowupSequence_schemeAt {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n ≤ s.length) :
    AlgebraicGeometry.IsNoetherian ((ambientBlowupSequence ι s hres hno hcen).obj n) :=
  (ambientEmbedding ι s hres hno hcen n).isNoetherian_ambient_of_le_length hn

theorem isClosedImmersion_embeddingIntoAmbientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) :=
  (ambientEmbedding ι s hres hno hcen n).emb_isClosedImmersion

theorem embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι := rfl

theorem embeddingIntoAmbientBlowupSequence_succ_comp_map {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1) ≫ (ambientBlowupSequence ι s hres hno hcen).map n =
      s.map n ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen n :=
  succAmbientEmbedding_comp_blowupMorphism hres hno s hcen n (ambientEmbedding ι s hres hno hcen n)

theorem ker_embeddingIntoAmbientBlowupSequence_succ {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) (n : ℕ) (hn : n < s.length) :
    (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).map n)
        ((ambientBlowupSequence ι s hres hno hcen).center n)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n).ker :=
  ker_succAmbientEmbedding_eq_strictTransform hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

theorem isPushforwardBlowupSeq_ambientBlowupSequence {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i),
        ¬ T ⊆ ((s.center i).support : Set ↥(s.obj i))) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups := by
  refine ⟨rfl, ⟨fun i _ => embeddingIntoAmbientBlowupSequence ι s hres hno hcen i,
    fun i _ => isClosedImmersion_embeddingIntoAmbientBlowupSequence ι s hres hno hcen i, ?_, ?_, ?_, ?_⟩⟩
  · show (s.isoZero.hom ≫ ι) ≫ 𝟙 X = s.isoZero.hom ≫ ι
    exact Category.comp_id _
  · intro i hi
    show embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1) ≫
        (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i =
      s.toSequenceOfBlowups.transitionMapSucc i ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen i
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact embeddingIntoAmbientBlowupSequence_succ_comp_map ι s hres hno hcen i
  · intro i _
    rfl
  · intro i hi
    show (embeddingIntoAmbientBlowupSequence ι s hres hno hcen (i + 1)).ker =
      Blowup.strictTransform ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.transitionMapSucc i)
        ((ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups.center i)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen i).ker
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen i hi

end FunctorialResolution.EmbeddedResolution
