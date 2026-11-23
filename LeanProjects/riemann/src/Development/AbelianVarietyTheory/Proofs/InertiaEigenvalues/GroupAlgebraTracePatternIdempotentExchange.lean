import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhIUnionTrans
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumGraphEqSumEntN
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrFirstPattern
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem tr_eJ_eq_tr_eJ' : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ →
      tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ hψ N k s hN χ hχ
  have key : ∀ i, i ≤ s →
      tr (GlobalTheory.GLm.ePat g N (GlobalTheory.GLm.phI k s i) (GlobalTheory.GLm.eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
    intro i
    induction i with
    | zero => intro _; exact GlobalTheory.GLm.FirstPattern.tr_first_pattern g ψ N k s hN χ hχ
    | succ n ih =>
      intro hn
      rw [GlobalTheory.RootExch.step g ψ hψ N k s (n + 1) hN (by omega) hn χ hχ]
      exact ih (by omega)
  rw [← GlobalTheory.GLm.ePat_last_eq_eJ g ψ N k s hN]
  exact key s le_rfl

end GlobalTheory.GLq
