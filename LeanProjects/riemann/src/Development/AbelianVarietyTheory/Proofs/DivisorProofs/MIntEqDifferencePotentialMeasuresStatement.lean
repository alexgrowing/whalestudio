import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqDifferencePotentialMeasures
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mInt_eq_difference_potential_measures : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (P : LocPot (M.X a)), IsPotential (M.A a) P → ∀ g : M.X a → ℝ, Continuous g → mInt (M.A a) (fun _ => P) g = ∫ x, g x ∂(potMeas I P 1) - ∫ x, g x ∂(potMeas I P (-1)) := by
  first | exact @GlobalTheory.Mean4O.CoverInt.mInt_eq_potMeas | exact GlobalTheory.Mean4O.CoverInt.mInt_eq_potMeas | (intros; apply GlobalTheory.Mean4O.CoverInt.mInt_eq_potMeas <;> assumption)
