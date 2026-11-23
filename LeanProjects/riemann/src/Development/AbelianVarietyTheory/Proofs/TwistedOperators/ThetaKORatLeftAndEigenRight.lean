import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaKO_rat_left_and_eigen_right : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h, thetaKO om (γ * g) (γ' * h) f = thetaKO om g h f) ∧ ∀ k k' (c : ℂ), om (k, k') f = c • f → ∀ g h, thetaKO om (g * k) (h * k') f = c * thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  refine ⟨fun γ hγ γ' hγ' g h => ?_, fun k k' c hc g h => ?_⟩
  ·

    have hprod : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres (g, h) f hf)
  ·
    have hprod : ((g * k, h * k') : GA D S × GA D T) = (g, h) * (k, k') := rfl
    unfold thetaKO
    rw [hprod, map_mul, Module.End.mul_apply, hc, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory
