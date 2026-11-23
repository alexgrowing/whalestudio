import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtOfLocalFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlagWholeSymbolReindexedStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag

set_option autoImplicit false

theorem GlobalTheory.TrivFlag.flagAt_wholeSym : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    ∃ e : Fin (2 * (D.R.f * O.N)) ≃ Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N),
      FlagAt (fun i => adlOf (O.Φ.C c) (O.met.hm c)
        (wholeSym (Function.update (ArIn.ind Sx) p true) (some R) (e i))) p := by
  intro h2 hH hRA hSW D O hO Sx R hR p hp c
  obtain ⟨e, he⟩ := GlobalTheory.T.local_flag_whole_symbol_reindexed h2 hH hRA hSW D O hO Sx R hR p hp c
  exact ⟨e, GlobalTheory.T.flag_at_of_local_flag _ _ _ _ _ p hp he⟩
