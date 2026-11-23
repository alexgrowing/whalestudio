import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGenerated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
  ∃ (S : Subring R) (ι₀ : (S ⧸ I.comap S.subtype) →+* R₀)
    (AS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj AS₀) (AS : Over (Sp S)) (_ : GrpObj AS) (iS : AS₀.left ⟶ AS.left)
    (BS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj BS₀) (BS : Over (Sp S)) (_ : GrpObj BS) (jS : BS₀.left ⟶ BS.left)
    (fS₀ : AS₀ ⟶ BS₀) (φA : A.left ⟶ AS.left) (φB : B.left ⟶ BS.left) (ψA : A₀.left ⟶ AS₀.left) (ψB : B₀.left ⟶ BS₀.left),
    Algebra.FiniteType ℤ S ∧ ι₀.comp (Ideal.Quotient.mk (I.comap S.subtype)) = π.comp S.subtype ∧ IsMonHom fS₀ ∧
    IsGrpPullback AS₀ AS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) iS ∧
    IsGrpPullback BS₀ BS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) jS ∧
    IsAbelianScheme AS ∧ SmoothOfRelativeDimension g AS.hom ∧ IsAbelianScheme BS ∧ SmoothOfRelativeDimension g' BS.hom ∧
    IsGrpPullback A AS (spMap S.subtype) φA ∧ IsGrpPullback B BS (spMap S.subtype) φB ∧
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA ∧ IsGrpPullback B₀ BS₀ (spMap ι₀) ψB ∧
    i ≫ φA = ψA ≫ iS ∧ j ≫ φB = ψB ≫ jS ∧ f₀.left ≫ ψB = ψA ≫ fS₀.left := by
  first | exact @GlobalTheory.AbHomDesc.abelian_hom_reduction_descends | exact GlobalTheory.AbHomDesc.abelian_hom_reduction_descends | (intros; apply GlobalTheory.AbHomDesc.abelian_hom_reduction_descends <;> assumption)
