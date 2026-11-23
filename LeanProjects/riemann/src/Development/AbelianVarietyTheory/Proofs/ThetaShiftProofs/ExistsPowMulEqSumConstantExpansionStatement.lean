import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  first | exact @GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | exact GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | (intros; apply GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum <;> assumption)
