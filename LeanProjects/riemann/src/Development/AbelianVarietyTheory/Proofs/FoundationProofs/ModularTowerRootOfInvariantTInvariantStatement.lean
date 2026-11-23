import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
