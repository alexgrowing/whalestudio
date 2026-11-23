import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameFlagCurvature
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_frame_flag_curvature : GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.SubQuotCurvature →
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (p q : ℕ) (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (a b : ℝ) (Y : Set E) (π : E → ι → ℂ)
    (AW eW : E → Matrix (Fin p) (Fin p) ℂ) (Aω eω : E → Matrix (Fin q) (Fin q) ℂ),
    IsHodgeFrame U ψ → 0 < a → 0 < b → IsFlagFamily Y U π AW → IsFlagFamily Y U π Aω →
    IsUnitaryFlagFrame Y (fun x => (a : ℂ) • quotGram (ψ x)) π AW eW →
    IsUnitaryFlagFrame Y (fun x => (b : ℂ) • -subGram (ψ x)) π Aω eω →
    ∀ y ∈ Y, ∀ lam : Fin (p + q) → ℝ, Antitone lam → ∀ ξ,
      0 ≤ diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW
            (fun i => lam (Fin.castAdd q i)) y) ξ +
          diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω
            (fun i => lam (Fin.natAdd p i)) y) ξ ∧
      (StrictAnti lam → secondForm ψ (π y) (fderiv ℂ π y ξ) ≠ 0 →
        0 < diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW
            (fun i => lam (Fin.castAdd q i)) y) ξ +
          diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω
            (fun i => lam (Fin.natAdd p i)) y) ξ) := by
  first | exact @GlobalTheory.HodgeHoriz.hodge_horiz | exact GlobalTheory.HodgeHoriz.hodge_horiz | (intros; apply GlobalTheory.HodgeHoriz.hodge_horiz <;> assumption)
