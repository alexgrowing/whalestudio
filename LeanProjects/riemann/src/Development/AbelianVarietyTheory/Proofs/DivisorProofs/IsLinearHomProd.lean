import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def coords : Set (Fin p → E) :=
  {c | ∃ n : ℕ, 0 < n ∧ ∃ x : Fin p → 𝓞 E, (∀ a, (x a : E) = n * c a) ∧
    ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)}

def lat : Submodule (𝓞 E) (Fin p → E) := Submodule.span (𝓞 E) (coords X)

theorem isLinearHom_prod (x : Fin p → 𝓞 E) :
    Serre.IsLinearHom (X.A true).t.act X.B.t.act (∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)) := by
  classical
  refine Finset.prod_induction _ (Serre.IsLinearHom (X.A true).t.act X.B.t.act)
    (fun f g hf hg => hf.mul hg) (Serre.IsLinearHom.one _ _) fun a _ => ?_
  exact (Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))

theorem intl_mem (x : Fin p → 𝓞 E) : (fun a => (x a : E)) ∈ lat X :=
  Submodule.subset_span ⟨1, one_pos, x, fun a => by simp, _, isLinearHom_prod X x, pow_one _⟩

end GlobalTheory.FlatCM.HomLat

end
