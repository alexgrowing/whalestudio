import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory

theorem rdU_mul_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r), rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  intro E _ _ _ H Dw l Xo c σ r U f f' k x
  classical
  by_cases h : x ∈ (U.X k).dom
  · have e := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
    exact e
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, mul_zero]

end GlobalTheory
