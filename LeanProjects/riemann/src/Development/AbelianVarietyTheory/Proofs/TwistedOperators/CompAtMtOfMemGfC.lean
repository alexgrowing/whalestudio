import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedHeis

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  rw [GfC, MonoidHom.mem_ker] at hk
  unfold compAt Formalism.L2.Theta.mt
  unfold infHom at hk
  unfold infPart
  rw [MonoidHom.comp_apply] at hk
  have e := congrArg (fun g => (Units.val g).map (θ τ)) hk
  simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  rw [← e]
  rfl

theorem om_fin_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ sS sT BS BT f P, IsThetaFunO ψ S T f → om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (κ, κ') f) P := by
  intro D ψ S T χS χT om hW θ hθ κ hκ κ' hκ' sS sT BS BT f P hf
  have h1 := fun τ => compAt_mt_of_mem_GfC θ S hκ τ
  have h2 := fun τ => compAt_mt_of_mem_GfC θ T hκ' τ
  have := (om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT κ κ' (fun τ => by rw [h1 τ, one_mul, mul_one]) (fun τ => by rw [h2 τ, one_mul, mul_one]) (fun τ => by rw [h1 τ, one_mul]) (fun τ => by rw [h2 τ, one_mul]) f hf P).2
  exact this

end GlobalTheory.OrientedHeis
