import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import GroundTheory.AutomorphicForms.GKModules.RightRegular
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace GlobalTheory.HCA

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev glG : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ := ⊤

abbrev glL : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := ⊤

theorem glH : IsExpLieAlgebra (glG E a) (glL E a) := isExpLieAlgebra_top

def glB : LinearMap.BilinForm ℝ (glL E a) :=
  LinearMap.mk₂ ℝ (fun X Y => ∑ w, (trace (X.1 * Y.1) w).re)
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add, Finset.sum_add_distrib])
    (fun r X Y => by simp [trace_smul, Finset.mul_sum])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add, Finset.sum_add_distrib])
    (fun r X Y => by simp [trace_smul, Finset.mul_sum])

def glK : Subgroup (glG E a) := (Unitary.toUnits : Kinf E a →* GL (Fin a) (Cinf E)).range.comap (glG E a).subtype

variable {E a} [IsTotallyComplex E]

def glRes (φ : GA E a → ℂ) (x : GA E a) : glG E a → ℂ := fun y => φ (x * infGL E a y.1)

end GlobalTheory.HCA

end
