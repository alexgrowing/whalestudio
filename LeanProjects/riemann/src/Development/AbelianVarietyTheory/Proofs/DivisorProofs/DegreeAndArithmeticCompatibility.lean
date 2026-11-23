import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightDegreeOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeAsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSelfIntersectionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveIffPlurisubharmonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeOfPrintsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.TiesOnObj

theorem ties_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ A T _ _ => TieDeg T ∧ TieM T A ∧ TieAr A := by
  intro h2 hH D O hC hf A T H h
  exact ⟨GlobalTheory.T.height_degree_of_hypotheses h2 hH D O hC hf A T H h, fun B hB u s hu hs =>
    ⟨GlobalTheory.T.geometric_degree_as_integral h2 hH D O hC hf A T H h B hB u s hu hs, fun hd hsm =>
      ⟨GlobalTheory.T.arithmetic_self_intersection_formula h2 hH D O hC hf A T H h B hB u s hu hs hd hsm, GlobalTheory.T.semipositive_iff_plurisubharmonic h2 hH D O hC hf A T H h B hB u s hu hs hd hsm⟩⟩,
    GlobalTheory.T.arithmetic_degree_of_known_theorems h2 hH D O hC hf A T H h⟩

end GlobalTheory.TiesOnObj
