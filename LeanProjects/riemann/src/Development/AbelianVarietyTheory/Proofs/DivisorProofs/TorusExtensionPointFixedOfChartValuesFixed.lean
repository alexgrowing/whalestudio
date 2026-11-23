import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorusExt

open GlobalTheory.BXOf ReciprocityTheory.ChartRestriction.G.DVR

theorem gtExt_eq_self_of_charVal_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  intro R _ _ D F _ _ σ hσ g hb J hJ hfix
  have hb' : extMap σ hσ ≫ g.b = g.b := Over.OverMorphism.ext hb
  have hφ0 : ∀ χ k, Spec.map (CommRingCat.ofHom σ) ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k := by
    intro χ k
    show (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, hb']
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [hb']
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  refine gt_ext_val ((gtExt_b σ hσ g).trans hb') fun χ y J' hJ' => ?_
  obtain rfl : y = closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hdel : ∀ ψ : Spec (CommRingCat.of F) ⟶ D.P.A.left, Spec.map (CommRingCat.ofHom σ) ≫ ψ = ψ →
      del D.P.L σ J J' ψ = del D.P.L (RingHom.id F) J J' ψ := by
    intro ψ h
    unfold del
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e₁ := val_nat (g.isGen χ) σ hJ hJ' (𝟙 _)
  have e₂ := val_nat (g.isGen χ) (RingHom.id F) hJ hJ' (𝟙 _)
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at e₂
  have hu : Units.map σ.toMonoidHom (sig F (charVal g χ (closedPoint F) J)) = sig F (charVal g χ (closedPoint F) J) :=
    Units.ext (hfix χ)
  have hu' : Units.map (RingHom.id F).toMonoidHom (sig F (charVal g χ (closedPoint F) J)) =
      sig F (charVal g χ (closedPoint F) J) := Units.ext rfl
  have key : sig F (charVal (gtExt D σ hσ g) χ (closedPoint F) J') = sig F (charVal g χ (closedPoint F) J') := by
    rw [gtExt_val σ hσ g χ hJ', extMap_left, ← Category.comp_id (spMap σ)]
    refine e₁.trans (Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ DegPre.gtε k)
      (hdel _ ((congrArg _ (Category.id_comp _)).trans ((hφ0 χ k).trans (Category.id_comp _).symm))))
      (hu.trans hu'.symm)) e₂.symm)
  exact Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of F)).hom.hom.toMonoidHom)
    (stalkClosedPointIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective key

end GlobalTheory.TorusExt
