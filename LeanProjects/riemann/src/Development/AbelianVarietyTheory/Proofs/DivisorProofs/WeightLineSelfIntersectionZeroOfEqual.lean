import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricPullDetDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.HermLB GlobalTheory.CovTop

namespace GlobalTheory.FlagZ.WeightDrop

theorem isSelfInter_wtLine_zero : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (lam : ι → Fin N → ℤ) (j : ℕ) (τ : ι), 1 ≤ j → j < N →
    (∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) = j → lam τ a = lam τ b) → (wtLine lam).IsSelfInter 0 := by
  intro P ι _ N lam j τ h₁ h₂ h
  classical
  have hX := (isArithVar_hasHh_unique ι N).1
  have := hX.isIntegral
  have hO := (smooth_dim_isArithVar_part ι {y // y ≠ ((τ, ⟨j, by omega⟩) : ι × Fin (N + 1))} N
    (fun y => y.1.1) (fun y => y.1.2)).2.2
  exact (isometric_wtLine_pull lam _ (coef_eq_zero lam τ j h₁ h₂ h)).symm.isSelfInter hX
    (GlobalTheory.ProjDrop.isSelfInter_zero_of_classicalTheorems P ℤ _ (Fl ι N) _ (flStr ι N) _ (dimFl ι N) hO hX (forget _) (toZ_ext _ _)
      (dim_closure_lt _ (by simp; omega) (by simpa using h₂)) _)

end GlobalTheory.FlagZ.WeightDrop
