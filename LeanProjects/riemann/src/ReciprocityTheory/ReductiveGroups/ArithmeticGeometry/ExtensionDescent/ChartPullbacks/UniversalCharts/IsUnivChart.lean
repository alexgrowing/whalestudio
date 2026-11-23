import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

def IsUnivChart {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) : Prop :=
  (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
    ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 →
      ∃! ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m

end ReciprocityTheory.ChartRestriction.G.Chart
