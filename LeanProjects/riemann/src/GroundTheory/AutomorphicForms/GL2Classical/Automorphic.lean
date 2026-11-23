import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.ZFinite
import GroundTheory.AutomorphicForms.GL2Classical.CuspConverse
import GroundTheory.AutomorphicForms.GL2Classical.ModerateGrowth

open NumberField Matrix CongruenceSubgroup ModularForm
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem exists_cuspForm_of_liftEquiv_mem_cuspForms
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∈ cuspForms ℚ 2) :
    ∃ F : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k, (F : ℍ → ℂ) = f :=
  exists_cuspForm_of_isCuspidal_liftEquiv f hf.2

end GL2Classical

end

end GroundTheory.Automorphic
