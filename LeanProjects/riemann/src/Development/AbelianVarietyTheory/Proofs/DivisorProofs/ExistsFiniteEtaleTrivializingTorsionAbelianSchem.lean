import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleTrivializingTorsionAbelianSchem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  first | exact @UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme | exact UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme
