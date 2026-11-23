import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAverageOverLifts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_average_over_lifts : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (x : Y.X) (d : ℕ) (z : ∀ a, Fin (d + 1) → M.X a) (g : ∀ σ, Pts Y σ → ℝ), IsClosed ({x} : Set Y.X) → I.Lists x z → M.κ * ∑ a, (∑ i, g (I.ε a) (I.pt a (z a i))) / ((d : ℝ) + 1) = (∑ σ : F →+* ℂ, ∑ᶠ (w : Pts Y σ) (_ : under w = x), g σ w) / ((Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ)) := by
  first | exact @GlobalTheory.Mean4O.mean_listed_eq | exact GlobalTheory.Mean4O.mean_listed_eq | (intros; apply GlobalTheory.Mean4O.mean_listed_eq <;> assumption)
