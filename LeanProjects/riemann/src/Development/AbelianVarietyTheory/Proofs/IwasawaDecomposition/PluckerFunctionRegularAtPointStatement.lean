import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerFunctionRegularAtPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_function_regular_at_point : ∀ (X : Scheme.{0}) [IsIntegral X] (y : X) (n : ℕ) (i : Fin n) (Δ : Fin n → GlobalTheory.Cartier.CartierDiv X) (t : Fin n → X.functionFieldˣ) (T : Matrix (Fin n) (Fin n) X.functionField) (By : Matrix (Fin n) (Fin n) (X.presheaf.stalk y)), (∀ a, (Δ a).IsEqn y (t a)) → (∀ a, T a a = t a) → (∀ a b, a < b → T a b = 0) → ∀ q, (-∑ a : Fin n, if (a : ℕ) < (i : ℕ) then Δ a else 0).RegularAt y (GlobalTheory.FlagEmb.plk (GlobalTheory.FlagAmple.PlkLoc.what₂ (T * By.map (algebraMap (X.presheaf.stalk y) X.functionField)) i) id q) := by
  first | exact @GlobalTheory.FlagAmple.PlkLoc.regularAt_plk_rows | exact GlobalTheory.FlagAmple.PlkLoc.regularAt_plk_rows | (intros; apply GlobalTheory.FlagAmple.PlkLoc.regularAt_plk_rows <;> assumption)
