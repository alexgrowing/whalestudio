import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule

open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothVecGl

theorem unitAct_glRel : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ),
    Formalism.REAL.GlRel (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b) := by
  intro n ε H _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  intro a b c d
  ext u
  have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
    (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
    n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
  rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
  split_ifs <;> simp [unitAct_coe]

end GlobalTheory.CompanionTheory.SmoothVecGl
