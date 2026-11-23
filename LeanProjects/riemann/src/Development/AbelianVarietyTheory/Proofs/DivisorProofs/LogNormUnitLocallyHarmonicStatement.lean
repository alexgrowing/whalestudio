import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormUnitLocallyHarmonic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_unit_locally_harmonic : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (h : Y.Fn) (x : M.X a), UnitAt (under (I.pt a x)) h → ∃ W : Set (M.X a), IsOpen W ∧ x ∈ W ∧ ∃ G : M.X a → ℂ, (M.A a).HoloOn W G ∧ ∀ y ∈ W, Real.log ‖ratVal h (I.pt a y)‖ = (G y).re := by
  first | exact @GlobalTheory.Mean4O.log_norm_ratVal_eq_re_holo | exact GlobalTheory.Mean4O.log_norm_ratVal_eq_re_holo | (intros; apply GlobalTheory.Mean4O.log_norm_ratVal_eq_re_holo <;> assumption)
