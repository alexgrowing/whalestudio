import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

def intCoordSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem intCoordSwap_mul_self : intCoordSwap * intCoordSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCoordSwap, Matrix.mul_apply, Fin.sum_univ_two]

example : intCoordSwap * intCoordSwap = 1 ∧ IsArithVar (⊥ : Ideal (MRing (dualBlocks (Fin 2)))) (1 + 1) ∧
    (∀ j, IsSmoothHerm (![fsLine 2] j)) ∧ IsSmoothHerm (fsLine 2) ∧
    IsSectionOn (⊥ : Ideal (MRing (dualBlocks (Fin 2)))) (fsLine 2) (Xc 2 0) :=
  ⟨intCoordSwap_mul_self, Inter.isArithVar_projLine, fun j => by fin_cases j; exact Inter.isSmoothHerm_fsLine 2,
    Inter.isSmoothHerm_fsLine 2, Inter.isSectionOn_Xc 2 0⟩

end

end GroundTheory.Heights₂.Heights
