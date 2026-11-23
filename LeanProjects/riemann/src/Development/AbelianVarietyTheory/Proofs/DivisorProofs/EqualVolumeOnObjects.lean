import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEqStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.EqVolObj

theorem w_eq_covol {D : D7} {O : Setup D} {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (h : O.Reads A T H)
    (c : O.s.Comp) : A.w c = GlobalTheory.TrueCx.covol ((O.s.U O.κ.σ₀).X c) := by
  rw [h.aux.w]
  rfl

theorem eqVol_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => EqVol A := by
  intro _ _ D O _ _ A T H h c c'
  have hp : 1 ≤ O.S.Dw.p := by have := O.S.p_eq; have := O.indef; omega
  have hq : 1 ≤ O.S.Dw.q := by have := O.S.rank_eq; have := O.S.p_eq; have := O.indef; omega
  rw [w_eq_covol h c, w_eq_covol h c']
  exact GlobalTheory.T.complexUniformisation_components_covolume_eq _ _ _ _ _ _ _ _ (O.s.U O.κ.σ₀) (GlobalTheory.ShFam.Lv.good_σ₀ O.κ) O.s.isUnf O.κ.good hp hq c c'

example : Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => EqVol A := eqVol_onObj

end GlobalTheory.EqVolObj
