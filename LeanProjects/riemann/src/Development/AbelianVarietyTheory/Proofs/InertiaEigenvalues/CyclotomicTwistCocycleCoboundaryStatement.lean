import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundary
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_twist_cocycle_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → ∀ j : ℤ, j ≠ 0 → ∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c → CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  first | exact @GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | exact GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | (intros; apply GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 <;> assumption)
