import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup ComplexConjugate
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Reduction RightCosetSpace

set_option linter.unusedSectionVars false

variable (μ : Measure (normOneGL ℚ 2)) [μ.IsHaarMeasure]

def adelicPetersson (φ₁ φ₂ : AdelicGL ℚ 2 → ℂ) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne ℚ 2), conj (φ₁ x) * φ₂ x ∂μ

variable {N : ℕ} [NeZero N] {k : ℤ}

def petersson (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : ℂ :=
  adelicPetersson μ (liftEquiv N k f.toSlashInvariantForm) (liftEquiv N k g.toSlashInvariantForm)

def scalarQ (c : ℚ) (hc : c ≠ 0) : GL (Fin 2) ℚ where
  val := !![c, 0; 0, c]
  inv := !![c⁻¹, 0; 0, c⁻¹]
  val_inv := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
  inv_val := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]

variable {N : ℕ} [NeZero N] {k : ℤ}

variable (p : ℕ) [NeZero p]

def heckeTranslate (ξ : GL (Fin 2) ℚ) : AdelicGL ℚ 2 :=
  finEmb ℚ 2 (finiteDiagonal ℚ 2 ξ) *
    realEmb (kGL (Real.sqrt p : ℂ) (by exact_mod_cast (Real.sqrt_pos.2 (natCast_pos_real p)).ne'))

variable [Fact p.Prime]

end GL2Classical

end

end GroundTheory.Automorphic
