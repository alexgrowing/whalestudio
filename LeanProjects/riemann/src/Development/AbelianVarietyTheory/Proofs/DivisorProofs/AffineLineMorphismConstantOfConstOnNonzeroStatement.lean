import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  first | exact @GlobalTheory.ConstAffineLine.eq_of_const_nonzero | exact GlobalTheory.ConstAffineLine.eq_of_const_nonzero | (intros; apply GlobalTheory.ConstAffineLine.eq_of_const_nonzero <;> assumption)
