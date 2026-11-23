import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Smooth

open NumberField Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem liftEquiv_spec_of_mdifferentiable
    (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (hhol : MDiff (f : ℍ → ℂ)) :
    IsLeftInvariant (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) ∧
      IsSmooth (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) ∧ IsKFinite (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) :=
  ⟨(liftEquiv N k f).2.isLeftInvariant,
    isSmooth_adelicLift (fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ) hhol,
    (liftEquiv N k f).2.isKFinite⟩

theorem liftEquiv_cuspForm_spec (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    IsLeftInvariant (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsSmooth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsKFinite (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      HasModerateGrowth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  obtain ⟨h1, h2, h3⟩ := liftEquiv_spec_of_mdifferentiable f.toSlashInvariantForm f.holo'
  exact ⟨h1, h2, h3, hasModerateGrowth_liftEquiv_cuspForm f, isCuspidal_liftEquiv_cuspForm f⟩

theorem mem_cuspForms_of_isZFinite (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hZ : IsZFinite (⟨(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ),
      (liftEquiv_cuspForm_spec f).2.1.1⟩ : archSmooth ℚ 2)) :
    (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∈ cuspForms ℚ 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := liftEquiv_cuspForm_spec f
  exact ⟨⟨h1, h2, h3, hZ, h4⟩, h5⟩

end GL2Classical

end

end GroundTheory.Automorphic
