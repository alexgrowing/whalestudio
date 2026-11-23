import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem yoneda_map_isLocallySurjective_of_etale_surjective (Y X : Scheme.{0}) (f : Y ⟶ X)
    (hf : Etale f) (hs : Surjective f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) where
  imageSieve_mem {U} s := by
    refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers PUnit (fun _ => pullback f s) (fun _ => pullback.snd f s)
      (fun x => ?_) (fun _ => inferInstance), ?_⟩
    · obtain ⟨y, hy⟩ := (inferInstance : Surjective (pullback.snd f s)).surj x
      exact ⟨⟨⟩, y, hy⟩
    · rintro V g ⟨j⟩
      exact ⟨pullback.fst f s, by simp; exact pullback.condition⟩

theorem isLocallySurjective_of_section {P Q : PSh} (f : P ⟶ Q) (s : Q ⟶ P) (h : s ≫ f = 𝟙 Q) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f :=
  Presheaf.isLocallySurjective_of_surjective _ f fun U q =>
    ⟨s.app U q, by simpa using ConcreteCategory.congr_hom (NatTrans.congr_app h U) q⟩

theorem isLocallySurjective_of_isPullback {P Q P' Q' : PSh} (a : P' ⟶ P) (f' : P' ⟶ Q')
    (f : P ⟶ Q) (b : Q' ⟶ Q) (hpb : IsPullback a f' f b)
    (hf : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' where
  imageSieve_mem {U} y := by
    refine Scheme.etaleTopology.superset_covering ?_ (Presheaf.imageSieve_mem _ f (b.app _ y))
    rintro V i ⟨t, ht⟩
    have hV := hpb.map ((evaluation _ _).obj (op V))
    obtain ⟨x, hx1, hx2⟩ := Types.exists_of_isPullback hV t (Q'.map i.op y)
      (by simpa [NatTrans.naturality_apply] using ht)
    exact ⟨x, hx2⟩

theorem locallySurjective_etale_section_baseChange :
    (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' :=
  ⟨yoneda_map_isLocallySurjective_of_etale_surjective,
   fun _ _ f s h => isLocallySurjective_of_section f s h,
   fun _ _ _ _ a f' f b h hf => isLocallySurjective_of_isPullback a f' f b h hf⟩

end GlobalTheory.EtC
