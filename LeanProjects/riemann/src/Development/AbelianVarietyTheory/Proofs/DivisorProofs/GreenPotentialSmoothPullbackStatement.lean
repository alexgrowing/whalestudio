import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenPotentialSmoothPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_potential_smooth_pullback : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (c : O.s.Comp) (R : ℝ), 2 ≤ R → ∀ (u : D.what₂.Tau → Fin O.N → ℝ) (V : Cover (O.var c)) (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, GlobalTheory.CxPts V.p σ → (T.M c).X (ε σ)), V.IsDown (h.man c) ε π → (T.M c).Smooth ((T.F c).phR R u) ∧ (∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ) y) ∧ ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ)).IsConj (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (T.F c).phR R u) σ')) := by
  first | exact @GlobalTheory.InterpChgCover.smooth_cInf_conj | exact GlobalTheory.InterpChgCover.smooth_cInf_conj | (intros; apply GlobalTheory.InterpChgCover.smooth_cInf_conj <;> assumption)
