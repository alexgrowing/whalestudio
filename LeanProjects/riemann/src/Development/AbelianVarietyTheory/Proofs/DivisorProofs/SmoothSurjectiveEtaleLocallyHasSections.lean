import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleQuasiSectionOfSmoothSchemeHomStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_loc_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  intro Y X f _ _ U y
  refine (loc_iff_etale_affine_points U (fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y) ?_).2 ?_
  · rintro V W g k ⟨x, hx⟩
    exact ⟨k ≫ x, by simp [Category.assoc, hx]⟩
  · intro u
    obtain ⟨V, s, hE, hu⟩ := GlobalTheory.T.exists_etale_quasiSection_of_smooth_scheme_hom f (y u) (f.surjective (y u))
    obtain ⟨v, hv⟩ := hu
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    let W := pullback (s ≫ f) y
    obtain ⟨z, hz⟩ := W.affineCover.covers w
    haveI := hE
    have hEt : Etale (pullback.snd (s ≫ f) y) := inferInstance
    refine ⟨_, W.affineCover.f (W.affineCover.idx w) ≫ pullback.snd (s ≫ f) y, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · simp [hz, hw2]
    · refine ⟨W.affineCover.f (W.affineCover.idx w) ≫ pullback.fst (s ≫ f) y ≫ s, ?_⟩
      simp only [Category.assoc]
      rw [show pullback.fst (s ≫ f) y ≫ s ≫ f = pullback.snd (s ≫ f) y ≫ y from pullback.condition]

end GlobalTheory.EtC
