import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerMore

theorem UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {U : Subgroup Γ} {a a' : Γ → Matrix (Fin n) (Fin n) k},
      UpperTheory.V.U3.MatIrr U a →
        ∀ (h : GL (Fin n) k),
          (∀ g ∈ U, a' g = (↑h : Matrix (Fin n) (Fin n) k) * a g * (↑h⁻¹ : Matrix (Fin n) (Fin n) k)) →
            UpperTheory.V.U3.MatIrr U a' := by
  intro Γ k _ _ n U a a' hirr h hconj
  refine UpperTheory.Reformulated.B.G5.matIrr_conj h (fun g hg => ?_) hirr
  rw [hconj g hg, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
