import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker
import GroundTheory.AutomorphicForms.RealGroupsIwasawa

namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix NormedSpace Complex MeasureTheory
open scoped Matrix.Norms.L2Operator

abbrev GL2C : Subgroup (GL (Fin 2) ℂ) := ⊤

noncomputable abbrev gl2C : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) := ⊤

theorem hGL2C : IsExpLieAlgebra GL2C gl2C := isExpLieAlgebra_top

noncomputable def toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : GL2C :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (((toGLC A hA : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := rfl

theorem GL2C_ext {g g' : GL2C}
    (h : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ((g' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def nC (z : ℂ) : GL2C := toGLC !![1, z; 0, 1] (by simp)

noncomputable def aC (t : ℝ) : GL2C :=
  toGLC !![(Real.exp t : ℂ), 0; 0, (Real.exp (-t) : ℂ)] (by
    simp [Matrix.det_fin_two_of])

noncomputable def zC (s : ℝ) : GL2C :=
  toGLC !![(Real.exp s : ℂ), 0; 0, (Real.exp s : ℂ)] (by
    simp [Matrix.det_fin_two_of])

noncomputable def dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : GL2C :=
  toGLC !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] (by
    simp [Matrix.det_fin_two_of, h₁.ne', h₂.ne'])

@[simp] theorem coe_nC (z : ℂ) :
    (((nC z : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, z; 0, 1] := rfl
@[simp] theorem coe_aC (t : ℝ) : (((aC t : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.exp t : ℂ), 0; 0, (Real.exp (-t) : ℂ)] := rfl
@[simp] theorem coe_zC (s : ℝ) : (((zC s : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.exp s : ℂ), 0; 0, (Real.exp s : ℂ)] := rfl
@[simp] theorem coe_dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (((dC d₁ d₂ h₁ h₂ : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] := rfl

abbrev U2 : Type := unitaryGroup (Fin 2) ℂ

theorem det_ne_zero_of_U2 (k : U2) : ((k : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
  intro h
  have h1 : (star (k : Matrix (Fin 2) (Fin 2) ℂ) * k).det = 1 := by
    rw [Matrix.UnitaryGroup.star_mul_self, Matrix.det_one]
  rw [Matrix.det_mul, h, mul_zero] at h1
  exact zero_ne_one h1

noncomputable def kC : U2 →* GL2C where
  toFun k := toGLC (k : Matrix (Fin 2) (Fin 2) ℂ) (det_ne_zero_of_U2 k)
  map_one' := by apply GL2C_ext; rfl
  map_mul' k k' := by apply GL2C_ext; rfl

@[simp] theorem coe_kC (k : U2) :
    (((kC k : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem coe_kC_inv (k : U2) :
    ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      star (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 k.2)

theorem continuous_kC : Continuous kC := by
  have hval : Continuous fun k : U2 => ((kC k : GL (Fin 2) ℂ)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : (fun k : U2 => ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun k : U2 => star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext k; exact coe_kC_inv k
    rw [e]
    exact continuous_star.comp continuous_subtype_val
  exact continuous_induced_rng.2 hval

noncomputable def tC (a b : ℝ) : U2 :=
  ⟨!![Complex.exp (a * I), 0; 0, Complex.exp (b * I)], by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : ∀ r : ℝ, Complex.exp (r * I) * (starRingEnd ℂ) (Complex.exp (r * I)) = 1 := fun r => by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, h]⟩

@[simp] theorem coe_tC (a b : ℝ) : ((tC a b : U2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.exp (a * I), 0; 0, Complex.exp (b * I)] := rfl

noncomputable def lE : gl2C := ⟨!![0, 1; 0, 0], Submodule.mem_top⟩

noncomputable def lEi : gl2C := ⟨!![0, I; 0, 0], Submodule.mem_top⟩

noncomputable def lF : gl2C := ⟨!![0, 0; 1, 0], Submodule.mem_top⟩

noncomputable def lFi : gl2C := ⟨!![0, 0; I, 0], Submodule.mem_top⟩

noncomputable def lH : gl2C := ⟨!![1, 0; 0, -1], Submodule.mem_top⟩

noncomputable def lHi : gl2C := ⟨!![I, 0; 0, -I], Submodule.mem_top⟩

noncomputable def lZ : gl2C := ⟨!![1, 0; 0, 1], Submodule.mem_top⟩

noncomputable def lZi : gl2C := ⟨!![I, 0; 0, I], Submodule.mem_top⟩

noncomputable def lK0 : gl2C := ⟨!![0, 1; -1, 0], Submodule.mem_top⟩

noncomputable def lK1 : gl2C := ⟨!![0, I; I, 0], Submodule.mem_top⟩

@[simp] theorem coe_lE : ((lE : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 0, 0] := rfl
@[simp] theorem coe_lEi : ((lEi : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, I; 0, 0] := rfl
@[simp] theorem coe_lF : ((lF : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 0; 1, 0] := rfl
@[simp] theorem coe_lFi : ((lFi : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 0; I, 0] := rfl
@[simp] theorem coe_lH : ((lH : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := rfl
@[simp] theorem coe_lHi : ((lHi : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![I, 0; 0, -I] := rfl
@[simp] theorem coe_lZ : ((lZ : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 1] := rfl
@[simp] theorem coe_lZi : ((lZi : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![I, 0; 0, I] := rfl
@[simp] theorem coe_lK0 : ((lK0 : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl
@[simp] theorem coe_lK1 : ((lK1 : gl2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, I; I, 0] := rfl

end GroundTheory.Automorphic.ArchWhittakerC
