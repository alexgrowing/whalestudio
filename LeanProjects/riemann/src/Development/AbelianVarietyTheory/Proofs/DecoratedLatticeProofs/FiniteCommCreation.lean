import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FinComm

theorem finite_comm_creation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hom g hg h hh f hf
  have hθ : IsInfFam θ := hP.inf
  have hg' : g⁻¹ ∈ GfC S := inv_mem hg
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨hom.om_pres _ f hf.1, fun τ z => ?_⟩, fun P => ⟨?_, ?_⟩⟩
  · have h0 := hf.2 τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  · refine (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) g h ?_ ?_ ?_ ?_ f hf.1 P).1 <;> intro τ
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg, Matrix.one_mul]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh, Matrix.one_mul]
  · exact GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T μ μ om hom θ hθ g hg h hh _ _ _ _ f P hf.1

end GlobalTheory.AdForm.FinComm

end
