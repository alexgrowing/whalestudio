import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecializationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionMemComponentGenericOfClosedValuationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro X S f e hf hef x x' hxx' hx
  obtain ⟨V, _, _, _, g, hgc, hgb⟩ := GlobalTheory.T.exists_valuationRing_dominating_specialization X x' x hxx'
  set p : Spec (CommRingCat.of V) ⟶ S := g ≫ f with hp
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p) f p := IsPullback.of_hasPullback f p
  let σ : Spec (CommRingCat.of V) ⟶ pullback f p := pullback.lift g (𝟙 _) (by simp [hp])
  let e' : Spec (CommRingCat.of V) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [Category.assoc, hef])
  have hσf : σ ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσq : σ ≫ pullback.fst f p = g := pullback.lift_fst _ _ _
  have he'f : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'q : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  haveI : Smooth f := hf
  have hf' : Smooth (pullback.snd f p) := inferInstance
  have key := GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback X S (pullback f p) (Spec (CommRingCat.of V)) f (pullback.snd f p) p
    (pullback.fst f p) e e' hf hpb hef he'f he'q
  have hc : σ (IsLocalRing.closedPoint V) ∈ {y : ↥(pullback f p) | y ∈ connectedComponentIn
      (pullback.snd f p ⁻¹' {pullback.snd f p y}) (e' (pullback.snd f p y))} := by
    rw [← key]
    rw [Set.mem_preimage]
    have h1 : (pullback.fst f p) (σ (IsLocalRing.closedPoint V)) = x := by
      rw [← hgc, ← hσq]
      rfl
    rw [h1]
    exact hx
  have hb := GlobalTheory.T.section_mem_component_generic_of_closed_valuation V (pullback f p) (pullback.snd f p) e' σ hf' he'f hσf hc
  rw [← key] at hb
  have : (pullback.fst f p) (σ (⊥ : PrimeSpectrum V)) = x' := by
    rw [← hgb, ← hσq]
    rfl
  rw [← this]
  exact hb

end GlobalTheory
