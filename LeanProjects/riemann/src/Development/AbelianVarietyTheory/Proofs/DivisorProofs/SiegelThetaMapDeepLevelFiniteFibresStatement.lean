import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaMapDeepLevelFiniteFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (g : ℕ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig (ℓ ^ j) f → QFin f := by
  first | exact @GlobalTheory.SiegThQF.finite_fibres | exact GlobalTheory.SiegThQF.finite_fibres | (intros; apply GlobalTheory.SiegThQF.finite_fibres <;> assumption)
