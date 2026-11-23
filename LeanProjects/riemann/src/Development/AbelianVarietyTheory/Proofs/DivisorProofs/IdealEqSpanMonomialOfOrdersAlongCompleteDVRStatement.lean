import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
import Development.AbelianVarietyTheory.Definitions.Divisors.USt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_eq_span_monomial_of_orders_along_completeDVR : ∀ (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e)) (a : Fin m → ℕ), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W, Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) → I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  first | exact @GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | exact GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr | (intros; apply GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr <;> assumption)
