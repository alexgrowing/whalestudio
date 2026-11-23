import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

noncomputable section

namespace GlobalTheory.GenericFibre

open Limits

theorem pullback_isPullback_of_eq {X Y' Z : Scheme.{0}} (a a' : X ⟶ Z) (b b' : Y' ⟶ Z) (ha : a = a') (hb : b = b') :
    IsPullback (pullback.fst a b) (pullback.snd a b) a' b' := by
  subst ha hb; exact IsPullback.of_hasPullback _ _

theorem isProjOver_genericFibre : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k), IsProjOver q → IsProjOver p → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y)
    (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s := by
  intro k _ B Y _ q p hq hp f hfq G j s H
  haveI : IsProper q := CommonModel.isProper_of_isProjOver hq
  obtain ⟨φ, hφ⟩ : ∃ φ : k →+* B.functionField, B.fromSpecStalk (genericPoint B) ≫ q = spMap φ :=
    ⟨(Spec.preimage (B.fromSpecStalk (genericPoint B) ≫ q)).hom, by simp [spMap]⟩
  have P : IsPullback (pullback.fst (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q))
      (pullback.snd (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q)) p (spMap φ) := by
    exact pullback_isPullback_of_eq _ _ _ _ hfq hφ
  have h1 := ProjSpace.isProjOver_of_isPullback_spMap φ P hp
  have h2 := ProjSpace.isProjOver_comp_of_isClosedImmersion
    (H.isoPullback.hom ≫ pullback.mapDesc f (B.fromSpecStalk (genericPoint B)) q) h1
  have e : (H.isoPullback.hom ≫ pullback.mapDesc f (B.fromSpecStalk (genericPoint B)) q) ≫
      pullback.snd (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q) = s := by
    simp only [pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact H.isoPullback_hom_snd
  rwa [e] at h2

end GlobalTheory.GenericFibre
