import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlagAdelicWholeSymbolStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationAdelicUnitHeightStatement

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag

theorem locFlag_whole : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    ∃ e : Fin (2 * (D.R.f * O.N)) ≃ Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N),
      LocFlag (fun i => adlOf (O.Φ.C c) (O.met.hm c)
        (wholeSym (Function.update (ArIn.ind Sx) p true) (some R) (e i))) p := by
  intro h1 h2 h3 h4 D O hO Sx R hR p hp c
  refine ⟨(finCongr (two_mul _)).trans finSumFinEquiv.symm, ?_⟩
  obtain ⟨hD, hlg⟩ := GlobalTheory.T.flag_compactification_adelic_unit_height (O.Φ.C c) (O.met.hm c) (Function.update (ArIn.ind Sx) p true) (some R)
    (D.R.f * O.N) p hp
  have := GlobalTheory.T.reversed_flag_local_height_log_formula (two_mul _) _ _ p (fun k x => hD k x) (fun k v hv ε y => hlg k v hv ε y)
    (GlobalTheory.T.half_flag_adelic_whole_symbol h1 h2 h3 h4 D O hO Sx R hR p hp c)
  convert this using 2 with i
  simp only [Equiv.trans_apply]
  rcases finSumFinEquiv.symm (finCongr (two_mul (D.R.f * O.N)) i) with k | k <;> rfl

end GlobalTheory.WholeFlag

end
