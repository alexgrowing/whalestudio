import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPotentialOfMetricExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_potential_of_metric_exists : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (R : O.Reads A T H) (c : O.s.Comp) (σ : Fin ((T.M c).n + 1)), ∃ (m : (GlobalTheory.TrueGeo.cxSt D.what₂.LL).Met (O.var c) ((R.man c).ε σ) (P.bd c)) (L : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)) (s : (T.M c).X σ → (T.M c).X σ → ℂ), IsPot ((R.man c).pt σ) m L ∧ ReciprocityTheory.AnForm.M.IsPotential ((T.M c).A σ) L ∧ ReciprocityTheory.AnForm.M.IsSection ((T.M c).A σ) L s ∧ ∃ (n : ℕ) (mu : Fin n → ℕ) (W : Fin n → Set ((T.M c).X σ)), ReciprocityTheory.AnForm.M.IsSNC ((T.M c).A σ) L s mu W ∧ (∀ i, 1 ≤ mu i) ∧ ⋃ i, W i = (T.M c).Z σ := by
  first | exact @GlobalTheory.BdSec.exists_bd_section | exact GlobalTheory.BdSec.exists_bd_section | (intros; apply GlobalTheory.BdSec.exists_bd_section <;> assumption)
