import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacter
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.patternGroup_subgroup_order_character : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ) (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) → (∃ H : Subgroup (Gn g N), (∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) ∧ Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧ (∀ M : Mt g N, InPat Φ M → IsUnit M) ∧ ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) → ∀ M M' : Mt g N, InPat Φ M → InPat Φ M' → sumAt E (M * M') = sumAt E M + sumAt E M' := by
  first | exact @GlobalTheory.GLm.Pattern.pattern_group | exact GlobalTheory.GLm.Pattern.pattern_group | (intros; apply GlobalTheory.GLm.Pattern.pattern_group <;> assumption)
