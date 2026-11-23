import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.AffinePreimageFibre

theorem isPullback_comp_mono {C : Type*} [Category C] {A B T : C} (f : A ⟶ B) (c : B ⟶ T) [Mono c] :
    IsPullback f (𝟙 A) c (f ≫ c) :=
  IsPullback.of_isLimit' ⟨by simp⟩
    (PullbackCone.IsLimit.mk _ (fun s => s.snd)
      (fun s => by
        rw [← cancel_mono c]
        simp only [Category.assoc]
        exact s.condition.symm)
      (fun s => by simp)
      (fun s m _ h2 => by simpa using h2))

theorem isAffineOpen_preimage_fibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  intro X Z p U m A q ι H W hW hWU
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let h : (W : Scheme) ⟶ Sp Γ(X, U.1) := p.resLE U.1 W hWU ≫ U.2.isoSpec.hom
  have hh : W.ι ≫ p = h ≫ chart U := by
    simp [h, chart, IsAffineOpen.fromSpec]
  have big := (isPullback_morphismRestrict ι W).paste_vert H
  rw [hh] at big
  have comm : (ι ∣_ W) ≫ h = ((ι ⁻¹ᵁ W).ι ≫ q) ≫ spMap (Ideal.Quotient.mk m) := by
    rw [← cancel_mono (chart U)]
    simpa [Category.assoc] using big.w
  have sq : IsPullback (ι ∣_ W) ((ι ⁻¹ᵁ W).ι ≫ q) h (spMap (Ideal.Quotient.mk m)) :=
    IsPullback.of_bot (v₂₁ := 𝟙 _) (by simpa using big) comm (isPullback_comp_mono _ _)
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk m)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsAffineHom (ι ∣_ W) := MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip inferInstance
  haveI : IsAffine (W : Scheme) := hW
  exact isAffine_of_isAffineHom (ι ∣_ W)

end GlobalTheory.AffinePreimageFibre
