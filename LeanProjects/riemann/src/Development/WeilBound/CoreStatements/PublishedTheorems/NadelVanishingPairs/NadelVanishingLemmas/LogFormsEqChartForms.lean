import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsEqChartForms
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.log_forms_eq_chart_forms : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (G : CartierDiv X) (y : X) (t : X.functionFieldˣ) (a : ℕ), IsLogChart Z U x J → y ∈ U → G.IsEqn y t → logAt Z G a y = chartForms (locRing y) x J t a := by
  first | exact @_root_.GlobalTheory.LogDR.ChartStalk.logAt_eq_chartForms | exact _root_.GlobalTheory.LogDR.ChartStalk.logAt_eq_chartForms | (intros; apply _root_.GlobalTheory.LogDR.ChartStalk.logAt_eq_chartForms <;> assumption)
