import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtFFApprox

variable {J : Type} [SmallCategory J] (D0 : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}} (g' : D0.obj j ⟶ B')

def pmap {k k' : Under j} (φ : k ⟶ k') : pushout g' (D0.map k.hom) ⟶ pushout g' (D0.map k'.hom) :=
  pushout.desc (pushout.inl _ _) (D0.map φ.right ≫ pushout.inr _ _)
    (by rw [pushout.condition, ← Category.assoc, ← D0.map_comp, Under.w φ])

@[reassoc (attr := simp)] lemma inl_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inl _ _ ≫ pmap D0 j g' φ = pushout.inl _ _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma inr_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inr _ _ ≫ pmap D0 j g' φ = D0.map φ.right ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

def arrF : Under j ⥤ Arrow CommRingCat.{0} where
  obj k := Arrow.mk (pushout.inr g' (D0.map k.hom))
  map {k k'} φ := Arrow.homMk' (D0.map φ.right) (pmap D0 j g' φ) (inr_pmap D0 j g' φ).symm
  map_id k := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp

@[simp] lemma arrF_obj_left (k : Under j) : ((arrF D0 j g').obj k).left = D0.obj k.right := rfl
@[simp] lemma arrF_obj_right (k : Under j) : ((arrF D0 j g').obj k).right = pushout g' (D0.map k.hom) := rfl
@[simp] lemma arrF_obj_hom (k : Under j) : ((arrF D0 j g').obj k).hom = pushout.inr g' (D0.map k.hom) := rfl
@[simp] lemma arrF_map_left {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).left = D0.map φ.right := rfl
@[simp] lemma arrF_map_right {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).right = pmap D0 j g' φ := rfl

variable {A B : CommRingCat.{0}} (ι0 : D0 ⟶ (Functor.const J).obj A) (g : A ⟶ B) (h : B' ⟶ B)
  (hnat : ∀ k : Under j, g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g)

def pdesc (k : Under j) : pushout g' (D0.map k.hom) ⟶ B := pushout.desc h (ι0.app k.right ≫ g) (hnat k)

def coc : arrF D0 j g' ⟶ (Functor.const (Under j)).obj (Arrow.mk g) where
  app k := Arrow.homMk (f := (arrF D0 j g').obj k) (g := Arrow.mk g) (ι0.app k.right) (pdesc D0 j g' ι0 g h hnat k)
    (pushout.inr_desc _ _ (hnat k)).symm
  naturality k k' φ := by
    ext : 1
    · simp only [Arrow.comp_left, Functor.const_obj_map, Arrow.id_left, Category.comp_id, Arrow.homMk_left, arrF_map_left]
      rw [ι0.naturality φ.right]
      simp
    · simp only [Arrow.comp_right, Functor.const_obj_map, Arrow.id_right, Category.comp_id, Arrow.homMk_right, arrF_map_right]
      apply pushout.hom_ext
      · simp [pdesc]
      · simp only [pdesc, inr_pmap_assoc, pushout.inr_desc]
        rw [ι0.naturality_assoc φ.right]
        simp

@[simp] lemma coc_app_left (k : Under j) : ((coc D0 j g' ι0 g h hnat).app k).left = ι0.app k.right := rfl
@[simp] lemma coc_app_right (k : Under j) : ((coc D0 j g' ι0 g h hnat).app k).right = pdesc D0 j g' ι0 g h hnat k := rfl

lemma snd_coc (k : Under j) : (Comma.snd (𝟭 _) (𝟭 _)).map ((coc D0 j g' ι0 g h hnat).app k) = pdesc D0 j g' ι0 g h hnat k := rfl

@[reassoc] lemma inl_pdesc (k : Under j) : pushout.inl _ _ ≫ pdesc D0 j g' ι0 g h hnat k = h := pushout.inl_desc _ _ _
@[reassoc] lemma inr_pdesc (k : Under j) : pushout.inr _ _ ≫ pdesc D0 j g' ι0 g h hnat k = ι0.app k.right ≫ g := pushout.inr_desc _ _ _

def leftOf (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) : Cocone (Under.forget j ⋙ D0) where
  pt := s.pt
  ι := { app := fun k => pushout.inr g' (D0.map k.hom) ≫ s.ι.app k
         naturality := fun k k' φ => by
           have hw := s.w φ
           simp only [Functor.comp_map, Comma.snd_map] at hw
           dsimp
           rw [← hw, Category.comp_id]
           simp }

@[simp] lemma leftOf_ι_app (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) (k : Under j) :
    (leftOf D0 j g' s).ι.app k = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k := rfl

def rightIsColimit (hP : IsPushout g' (ι0.app j) h g) (hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j))) :
    IsColimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCocone (Cocone.mk (Arrow.mk g) (coc D0 j g' ι0 g h hnat))) where
  desc s := hP.desc (pushout.inl _ _ ≫ s.ι.app (Under.mk (𝟙 j))) (hL.desc (leftOf D0 j g' s)) (by
      have := hL.fac (leftOf D0 j g' s) (Under.mk (𝟙 j))
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [pushout.condition_assoc]
      simp only [Under.mk_right] at this
      rw [this]
      simp)
  fac s k := by
    dsimp
    apply pushout.hom_ext
    · have hw := s.w (Under.homMk k.hom (by simp) : Under.mk (𝟙 j) ⟶ k)
      simp only [Functor.comp_map, Comma.snd_map, arrF_map_right] at hw
      rw [snd_coc, inl_pdesc_assoc, IsPushout.inl_desc, ← hw]
      exact inl_pmap_assoc D0 j g' _ _
    · have := hL.fac (leftOf D0 j g' s) k
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [snd_coc, inr_pdesc_assoc, IsPushout.inr_desc, this]
  uniq s m hm := by
    apply hP.hom_ext
    · rw [IsPushout.inl_desc]
      have h1 := hm (Under.mk (𝟙 j))
      dsimp at h1
      rw [← h1, snd_coc, inl_pdesc_assoc]
    · rw [IsPushout.inr_desc]
      apply hL.hom_ext
      intro k
      have h1 := hL.fac (leftOf D0 j g' s) k
      have h2 := hm k
      dsimp at h1 h2 ⊢
      rw [h1, ← h2, snd_coc, inr_pdesc_assoc]

end GlobalTheory.EtFFApprox

open GlobalTheory.EtFFApprox in

theorem GlobalTheory.EtC.etFF_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  intro A B g hg
  obtain ⟨J, _, _, D0, ι0, ⟨hc⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨j, B', g', h, hg', hP⟩ := GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit J D0 (Cocone.mk A ι0) hc B g hg
  have hb := GlobalTheory.EtC.etFF_basic
  haveI := hb.1.2.1
  have hP' : IsPushout g' (ι0.app j) h g := hP
  have hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm hc
  have hnat : ∀ (k : Under j), g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g := by
    intro k
    rw [← Category.assoc, ι0.naturality k.hom]
    simpa using hP'.w
  refine ⟨Under j, inferInstance, inferInstance, arrF D0 j g', coc D0 j g' ι0 g h hnat, ⟨?_⟩, fun k => ?_⟩
  · exact Comma.fstSndJointlyReflectColimit hL (rightIsColimit D0 j g' ι0 g h hnat hP' hL)
  · have hk : EtFF (pushout.inr g' (D0.map k.hom)) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout g' (D0.map k.hom)).flip hg'
    exact ⟨hk, hft k.right, hb.2.2 _ _ _ hk (hft k.right)⟩
