import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

namespace GlobalTheory

theorem exists_holUnif_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  intro A _ g e Λ he hd hf hk
  refine ⟨⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩,
    { ex := e
      ex_add := he.1
      ex_onto := he.2.1
      Λ := Λ
      ker := hk
      discrete := hd
      full := hf
      hol := fun U f => by
        have h := he.2.2.1 U f
        simpa using h
      fr := fun _ _ => 1
      fr_hol := fun _ => differentiableOn_const _
      fr_ne := fun _ _ _ => one_ne_zero
      fr_compat := fun i j z h => by
        show (1 : ℂ) = _
        exact ((_root_.mul_one _).trans (valAt'_one _ h)).symm }, rfl⟩

end GlobalTheory
