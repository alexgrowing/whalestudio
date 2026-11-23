import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfRefinesPolarisedData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_of_refines_polarisedData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  first | exact @GlobalTheory.TInj.FromRefine.from_of_refines | exact GlobalTheory.TInj.FromRefine.from_of_refines | (intros; apply GlobalTheory.TInj.FromRefine.from_of_refines <;> assumption)
