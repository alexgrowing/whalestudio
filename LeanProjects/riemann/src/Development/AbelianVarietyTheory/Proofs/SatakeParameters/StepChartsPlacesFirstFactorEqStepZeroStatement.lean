import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepChartsPlacesFirstFactorEqStepZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧ ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  first | exact @GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | exact GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | (intros; apply GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero <;> assumption)
