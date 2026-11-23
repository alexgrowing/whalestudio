import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le : ∀ (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ), (∀ k, ψ₀ k ≠ 1) → admLq D → TieAdmG D → 100 ≤ D.R.r → (∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k) → ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) → locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ 3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) * Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) + (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := by
  first | exact @GlobalTheory.PropWU.propW_eUk | exact GlobalTheory.PropWU.propW_eUk | (intros; apply GlobalTheory.PropWU.propW_eUk <;> assumption)
