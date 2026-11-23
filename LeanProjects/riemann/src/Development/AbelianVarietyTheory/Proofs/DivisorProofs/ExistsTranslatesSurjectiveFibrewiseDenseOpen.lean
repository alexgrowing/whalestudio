import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslateSurj

theorem surjective_of_factor {X Y Z : Scheme.{0}} (p : X ⟶ Y) (O : X.Opens) (g : Z ⟶ X) (q : Z ⟶ Y)
    (hg : g ≫ p = q) (hq : Surjective q) (hO : ∀ z, g z ∈ O) : Surjective (O.ι ≫ p) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hq.surj y
  refine ⟨⟨g z, hO z⟩, ?_⟩
  rw [← hg]
  rfl

end GlobalTheory.TranslateSurj

namespace GlobalTheory.TranslateSurj

theorem exists_translates_surjective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  intro S A _ hA V B j hjV hBs hBg
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI := hBs
  haveI := hBg
  haveI : GeometricallyConnected B.hom := GlobalTheory.geometricallyConnected_of_geometricallyIntegral _
  haveI : Smooth (fst (A ⊗ A) B ≫ fst A A).left := by
    show Smooth (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom); infer_instance
  haveI : GeometricallyConnected (fst (A ⊗ A) B ≫ fst A A).left := by
    show GeometricallyConnected (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    exact GeometricallyConnected.comp _ _
  haveI : GeometricallyIntegral (fst (A ⊗ A) B ≫ fst A A).left := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : Surjective (fst A B).left := by
    show Surjective (pullback.fst A.hom B.hom); infer_instance
  have key : ∀ (a₀ : A ⊗ B ⟶ A) (w : (A ⊗ A) ⊗ B ⟶ A),
      lift (lift (fst A B) a₀) (snd A B) ≫ w = snd A B ≫ j →
      Surjective ((w.left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
    intro a₀ w hw
    refine surjective_of_factor _ _ (lift (lift (fst A B) a₀) (snd A B)).left (fst A B).left ?_ hq ?_
    · rw [← Over.comp_left]; congr 1; simp
    · intro z
      show w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) ∈ V
      have e : w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) = j.left ((snd A B).left z) := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw, Over.comp_left, Scheme.Hom.comp_apply]
      rw [e]; exact hjV _
  refine GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ ?_ ?_) ?_) ?_
  · refine key ((fst A B)⁻¹ * (snd A B ≫ j)) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key ((snd A B ≫ j)⁻¹ * fst A B) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]

end GlobalTheory.TranslateSurj
