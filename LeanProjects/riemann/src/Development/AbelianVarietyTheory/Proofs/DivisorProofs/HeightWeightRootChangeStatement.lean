import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_weight_root_change : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (u : D.what₂.Tau → Fin O.N → ℝ) (x : (O.var c).X), IsClosed ({x} : Set (O.var c).X) → O.htWt (O.rootH c) u x = O.htWt (O.root0 c ∅) u x + (∑ σ : D.what₂.LL →+* ℂ, ∑ᶠ (w : Pts (O.var c) σ) (_ : under w = x), O.chg c none u σ w) / ((Module.finrank ℚ D.what₂.LL : ℝ) * (Nat.card {y : AlgPt (O.var c) // below y.1 = x} : ℝ)) := by
  first | exact @GlobalTheory.Mean4O.htWt_rootH_eq | exact GlobalTheory.Mean4O.htWt_rootH_eq | (intros; apply GlobalTheory.Mean4O.htWt_rootH_eq <;> assumption)
