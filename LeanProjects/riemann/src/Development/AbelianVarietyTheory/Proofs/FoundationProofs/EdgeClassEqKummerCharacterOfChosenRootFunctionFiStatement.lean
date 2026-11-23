import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
