import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimension
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_trdeg_eq_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim | exact GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim <;> assumption)
