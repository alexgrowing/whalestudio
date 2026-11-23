import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerResidueMemAdjoinUnit
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_residue_mem_adjoin_unit : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (α γ : V) (ϖ : T) (m : ℕ), Irreducible ϖ → 0 < m → IsUnit γ →
    α ^ m = γ * algebraMap T V ϖ →
    (∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h') →
    (∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧ Polynomial.aeval α g * v = Polynomial.aeval α f) →
    ∀ v : V, IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  first | (exact @GlobalTheory.kummer_residue_mem_adjoin) | (exact GlobalTheory.kummer_residue_mem_adjoin) | (intros; apply GlobalTheory.kummer_residue_mem_adjoin  <;> assumption)
