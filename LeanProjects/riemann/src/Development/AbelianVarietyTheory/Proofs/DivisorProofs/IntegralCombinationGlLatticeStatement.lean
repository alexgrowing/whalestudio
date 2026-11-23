import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationGlLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open ValuativeRel
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_combination_gl_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    (∀ (X : Matrix (Fin n) (Fin d) k) (c : k), c ≠ 0 → ∃ h : GL (Fin d) k, ∀ Y : Matrix (Fin n) (Fin d) k,
      (∃ (A : Matrix (Fin n) (Fin n) k) (B : Matrix (Fin n) (Fin d) k), (∀ i j, A i j ∈ 𝒪[k]) ∧ (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔
        ∀ i j, (Y * (h : Matrix (Fin d) (Fin d) k)) i j ∈ 𝒪[k]) →
    ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    ∃ A : Set (Matrix (Fin n) (Fin d) k → ℂ), A.Finite ∧ (∀ a ∈ A, a ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) ∧
      ∀ φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k), (∀ g ∈ K, ∀ Y, φ ((g : Matrix (Fin n) (Fin n) k) * Y) = φ Y) →
        φ ∈ Submodule.span ℂ {χ : Matrix (Fin n) (Fin d) k → ℂ | ∃ a ∈ A, ∃ h : GL (Fin d) k, χ = fun Y => a (Y * (h : Matrix (Fin d) (Fin d) k))} := by
  first | exact @GlobalTheory.SBInvSpan.span_translates_of_invariant | exact GlobalTheory.SBInvSpan.span_translates_of_invariant | (intros; apply GlobalTheory.SBInvSpan.span_translates_of_invariant <;> assumption)
