import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCosets
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCommute
import GroundTheory.AutomorphicForms.GL2Classical.HeckePetersson
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatake
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatakeRep

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem translateSpan_le_cuspForms (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ≤ cuspForms ℚ 2 := by
  rw [translateSpan, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  have h := mem_cuspForms.1 (liftEquiv_mem_cuspForms f)
  exact ⟨h.1.rightTranslate_finEmb g, h.2.translate _⟩

end GL2Classical

end

end GroundTheory.Automorphic
