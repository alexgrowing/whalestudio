import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def ETSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

def ETPointStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) [Module (𝓞 E) D.toPre.X] (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ β : SymB cj D.toPre.X, (∀ a b, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf D.toPre Q a b) →
    (∀ a, (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) →
    (∀ a, 0 ≤ (β : D.toPre.X →ₗ[ℤ] D.toPre.X →ₗ[ℤ] ℝ) a a) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (R' R₀ : ℕ), 2 ≤ R' → 2 ≤ R₀ → R₀ ∣ R' → ∀ (r : ℕ) (y : Fin r → D.toPre.X),
      (∀ a : D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : D.toPre.X, a = u + R₀ • t) →
    ∀ (s : Fin r → Fam D.toPre F (R' ^ 2)) (w : Fin r → F),
      (∀ b (α : D.toPre.X), (∀ z : D.toPre.X, α ≠ y b + R' • z) → ∀ j, ((s b).s α).f j = 0) →
      (∀ b, NuGe D Q F v (R' ^ 2) (s b) 0) → (∀ b, ValAt0 D F v (R' ^ 2) (s b) (w b)) →
      ∀ q : ℚ, (q : ℝ) ≤ phiC cj β / (R' ^ 2 : ℝ) → ((q : ℚ) : WithTop ℚ) ≤ ∑ b, v (w b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
