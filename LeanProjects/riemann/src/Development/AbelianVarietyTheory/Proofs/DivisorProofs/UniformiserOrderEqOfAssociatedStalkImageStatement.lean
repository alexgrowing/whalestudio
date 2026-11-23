import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserOrderEqOfAssociatedStalkImage
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  first | exact @GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | exact GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated | (intros; apply GlobalTheory.UPoinc.uOrdEq_stalkHom_of_associated <;> assumption)
