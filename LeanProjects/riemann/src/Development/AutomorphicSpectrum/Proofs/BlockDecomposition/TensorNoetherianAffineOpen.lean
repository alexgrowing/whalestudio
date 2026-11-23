import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem krull_noeth_chart : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  intro X J Z ψ hψ V hV U hU h
  have hft : ((ψ ≫ J.subschemeι).appLE V U h).hom.FiniteType := by
    haveI : LocallyOfFiniteType ψ := inferInstance
    haveI : LocallyOfFiniteType (ψ ≫ J.subschemeι) := inferInstance
    exact LocallyOfFiniteType.finiteType_appLE (ψ ≫ J.subschemeι) hV hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  intro R _ _ _
  haveI : Algebra.FiniteType Γ(X, V) Γ(Z, U) := by
    exact hft
  haveI : Algebra.FiniteType R (R ⊗[Γ(X, V)] Γ(Z, U)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing R _

end GlobalTheory.CompanionTheory.GE
