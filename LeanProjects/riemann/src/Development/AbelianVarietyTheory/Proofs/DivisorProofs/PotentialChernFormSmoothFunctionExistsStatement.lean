import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChernFormSmoothFunctionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_chern_form_smooth_function_exists : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (R : O.Reads A T H) (c : O.s.Comp) (σ : Fin ((T.M c).n + 1)) (m : (GlobalTheory.TrueGeo.cxSt D.what₂.LL).Met (O.var c) ((R.man c).ε σ) (P.bd c)) (L : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)), IsPot ((R.man c).pt σ) m L → ReciprocityTheory.AnForm.M.IsPotential ((T.M c).A σ) L → ∃ g : (T.M c).X σ → ℝ, ((T.M c).A σ).Smooth g ∧ LeviEq ((T.M c).A σ) L ((T.F c).th A.dir σ + ((T.F c).a σ).rsmul (-1) + ReciprocityTheory.AnForm.M.LocPot.ofFun g) := by
  first | exact @GlobalTheory.BdClass.bd_form_eq | exact GlobalTheory.BdClass.bd_form_eq | (intros; apply GlobalTheory.BdClass.bd_form_eq <;> assumption)
