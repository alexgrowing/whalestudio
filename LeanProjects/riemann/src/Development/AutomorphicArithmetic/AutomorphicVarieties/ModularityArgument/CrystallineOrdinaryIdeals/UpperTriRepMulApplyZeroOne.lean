import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.UpperTriCoord

variable {G B : Type} [Group G] [CommRing B]

theorem entry_mul (ρ : G →* GL (Fin 3) B) (g h : G) (i j : Fin 3) :
    (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ∑ k, (ρ g : Matrix (Fin 3) (Fin 3) B) i k * (ρ h : Matrix (Fin 3) (Fin 3) B) k j := by
  rw [map_mul, Units.val_mul, Matrix.mul_apply]

section Tri

variable (ρ : G →* GL (Fin 3) B) (hT : ∀ g i j, j < i → (ρ g : Matrix (Fin 3) (Fin 3) B) i j = 0)
include hT

theorem diag_mul (g h : G) (i : Fin 3) :
    (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i i =
      (ρ g : Matrix (Fin 3) (Fin 3) B) i i * (ρ h : Matrix (Fin 3) (Fin 3) B) i i := by
  rw [entry_mul, Fin.sum_univ_three]
  fin_cases i
  · simp [hT h 1 0 (by decide), hT h 2 0 (by decide)]
  · simp [hT g 1 0 (by decide), hT h 2 1 (by decide)]
  · simp [hT g 2 0 (by decide), hT g 2 1 (by decide)]

def dg (i : Fin 3) : G →* Bˣ where
  toFun g := ⟨(ρ g : Matrix (Fin 3) (Fin 3) B) i i, (ρ g⁻¹ : Matrix (Fin 3) (Fin 3) B) i i,
    by rw [← diag_mul ρ hT, mul_inv_cancel, map_one]; simp,
    by rw [← diag_mul ρ hT, inv_mul_cancel, map_one]; simp⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; exact diag_mul ρ hT g h i

end Tri

end GlobalTheory.UpperTriCoord
