import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cech_level_eqv_of_integral_pullback :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  intro R _ F Y X Y' X' a f' f b hab hf H m hm n
  have hf' : IsIntegralHom f' := MorphismProperty.of_isPullback (P := @IsIntegralHom) hab hf

  have hn : IsPullback (m.app n) ((cechAug f').app n) ((cechAug f).app n) (yoneda.map b) :=
    hm.map ((evaluation SimplexCategoryᵒᵖ PSh).obj n)
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y X f hf n
  obtain ⟨Z', π', e', hπ', he'⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y' X' f' hf' n
  have hh : IsIntegralHom (π ≫ f) := inferInstance
  have hh' : IsIntegralHom (π' ≫ f') := inferInstance
  let φ : Z' ⟶ Z := yoneda.preimage (e'.hom ≫ m.app n ≫ e.inv)
  have hφ : yoneda.map φ = e'.hom ≫ m.app n ≫ e.inv := yoneda.map_preimage _
  have hsqY : IsPullback (yoneda.map φ) (yoneda.map (π' ≫ f')) (yoneda.map (π ≫ f)) (yoneda.map b) := by
    refine IsPullback.of_iso hn e'.symm e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hφ]
    · simp [← he']; exact Category.comp_id _
    · simp [← he]; exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hsq : IsPullback φ (π' ≫ f') (π ≫ f) b := by
    refine IsPullback.of_map yoneda ?_ hsqY
    apply yoneda.map_injective
    simpa using hsqY.w
  have hE := H Z Z' (π ≫ f) (π' ≫ f') φ hh hsq
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  have hdec : disc.map (m.app n) = disc.map e'.inv ≫ sch.map φ ≫ disc.map e.hom := by
    change _ = disc.map e'.inv ≫ disc.map (yoneda.map φ) ≫ disc.map e.hom
    simp only [hφ, ← Functor.map_comp, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hdec]
  exact (hcomp _ _ _ _ _).1 (hiso _ _ (disc.map e'.inv) inferInstance)
    ((hcomp _ _ _ _ _).1 hE (hiso _ _ (disc.map e.hom) inferInstance))

end GlobalTheory
