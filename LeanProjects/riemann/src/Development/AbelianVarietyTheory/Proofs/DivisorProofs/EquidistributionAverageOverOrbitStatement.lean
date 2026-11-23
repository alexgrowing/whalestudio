import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributionAverageOverOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistribution_average_over_orbit : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (w : V.G), IsClosed ({w} : Set V.G) → ∀ (d : ℕ) (z : ∀ a, Fin (d + 1) → M.X a), I.Lists (V.π w) z → ∀ g : M.Fun, (M.κ * ∑ a, (∑ i, g a (z a i)) / ((d : ℝ) + 1)) * Nat.card (V.X.residueField (V.j w) →+* ℂ) = ∑ᶠ σ, ∑ᶠ x ∈ {x : CxPts V.p σ | x.1 (IsLocalRing.closedPoint ℂ) = V.j w}, M.pull ε π g σ x := by
  first | exact @GlobalTheory.Mean4O.mean_listed_eq_cover | exact GlobalTheory.Mean4O.mean_listed_eq_cover | (intros; apply GlobalTheory.Mean4O.mean_listed_eq_cover <;> assumption)
