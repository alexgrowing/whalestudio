import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_lift_level : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  first | exact @GlobalTheory.FNCongLift.cong_lift | exact GlobalTheory.FNCongLift.cong_lift | (intros; apply GlobalTheory.FNCongLift.cong_lift <;> assumption)
