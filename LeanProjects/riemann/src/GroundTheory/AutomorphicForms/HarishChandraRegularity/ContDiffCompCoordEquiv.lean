import Mathlib
import GroundTheory.AutomorphicForms.GKModules.RightRegular

namespace GroundTheory.Automorphic

open scoped ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

noncomputable def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] 𝔤 :=
  (EuclideanSpace.equiv (Fin d) ℝ).trans b.equivFun.symm.toContinuousLinearEquiv

theorem coordEquiv_apply {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (x : EuclideanSpace ℝ (Fin d)) :
    coordEquiv b x = ∑ j, x j • b j := by
  simp [coordEquiv, Module.Basis.equivFun_symm_apply]

theorem coordEquiv_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : coordEquiv b 0 = 0 :=
  map_zero _

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem contDiff_comp_coordEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : G → F} (hf : h.IsSmoothFun f) (g : G) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => f (g * h.expG (coordEquiv b x))) :=
  ((h.isSmoothFun_iff).1 hf g).comp (coordEquiv b).contDiff

end IsExpLieAlgebra

end GroundTheory.Automorphic
