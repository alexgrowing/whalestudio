import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusReciprocityUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonrealCharFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishOfMultInvariant
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

theorem GlobalTheory.LiftLowerLoc.form_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (ν β : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ (ℓ : Fin a → k), ℓ ≠ 0 → ∀ (ψv : AddChar k ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin a) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ (z : Fin (a + b) → k) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) →
      Bf = 0 :=
  GlobalTheory.LiftLowerLoc.loc_of_parts GlobalTheory.MultSupp.vanish_of_mult_invariant GlobalTheory.T.frobenius_reciprocity_unitary GlobalTheory.T.nonreal_char_functional_unique
