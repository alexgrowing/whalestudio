import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosets
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets : ∀ {H : Type} [Group H] (a : H → ℂ), (Function.support a).Finite → ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  first | exact @GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | exact GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | (intros; apply GlobalTheory.ConjRegroup.finsum_eq_finsum_classes <;> assumption)
