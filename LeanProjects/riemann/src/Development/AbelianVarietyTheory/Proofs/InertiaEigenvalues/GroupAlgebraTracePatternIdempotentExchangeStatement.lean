import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchange
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
