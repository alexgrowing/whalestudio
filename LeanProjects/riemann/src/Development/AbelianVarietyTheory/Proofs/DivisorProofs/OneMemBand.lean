import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import GroundTheory.AutomorphicForms.ReductionCore

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def absDetA (g : GA E a) : ℝ :=
  GroundTheory.Automorphic.Reduction.adeleAbs ((Matrix.GeneralLinearGroup.det g : (Ad E)ˣ) : Ad E)

theorem absDetA_pos (g : GA E a) : 0 < absDetA g := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det g)]
  exact ((GroundTheory.Global.IdeleGroup.ideleModule E) (Matrix.GeneralLinearGroup.det g)).2

theorem absDetA_one : absDetA (1 : GA E a) = 1 := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det (1 : GA E a)), map_one, map_one]
  rfl

variable (E a) in

def band : Set (GA E a) := {g | 1 ≤ absDetA g ∧ absDetA g ≤ 2}

theorem one_mem_band : (1 : GA E a) ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_one]; norm_num

end GlobalTheory.HCF

end
