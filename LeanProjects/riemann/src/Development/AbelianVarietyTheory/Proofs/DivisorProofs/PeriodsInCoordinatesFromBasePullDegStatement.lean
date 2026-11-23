import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDeg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁), Function.Injective ρ → ∀ (Q : DegPre V) (D : DegPre V₁) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X), (∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b)) → GlobalTheory.UChart.TauIn Q τ₀ s ε → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ib → ∃ τ₁ : GlobalTheory.UChart.Gens D, GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ ∧ GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  first | exact @GlobalTheory.USep.tauIn_fromBase_pull | exact GlobalTheory.USep.tauIn_fromBase_pull | (intros; apply GlobalTheory.USep.tauIn_fromBase_pull <;> assumption)
