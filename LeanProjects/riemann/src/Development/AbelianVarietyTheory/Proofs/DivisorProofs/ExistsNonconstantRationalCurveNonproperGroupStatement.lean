import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  first | exact @GlobalTheory.RatCurve.exists_rational_curve | exact GlobalTheory.RatCurve.exists_rational_curve | (intros; apply GlobalTheory.RatCurve.exists_rational_curve <;> assumption)
