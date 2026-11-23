import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FDMSubCompact
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem theta_bounded (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∃ B : ℝ, ∀ w, ‖f w‖ ≤ B := by
  obtain ⟨K, hK, hFK⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf.cont.norm.continuousOn)
  refine ⟨B, fun w => ?_⟩
  obtain ⟨g, hg, -⟩ := Formalism.IndefR.PHeisFC.exU T S w
  obtain ⟨γ, hγ⟩ := g.2
  have h1 : f (g +ᵥ w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w := by
    rw [AddSubgroup.vadd_def, vadd_eq_add, ← hγ]
    exact hf.quasi γ w
  have h2 := hB _ (hFK hg)
  rw [h1, norm_mul, Formalism.IndefR.Fin.psi_norm hψ, one_mul, norm_norm] at h2
  exact h2

end Formalism.IndefR.Eqv

end
