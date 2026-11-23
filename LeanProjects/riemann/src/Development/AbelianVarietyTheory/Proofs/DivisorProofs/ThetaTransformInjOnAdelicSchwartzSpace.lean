import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans

namespace ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInj

theorem schr_reindex {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (σ : κ ≃ κ') (w : (κ' → R) × (κ' → R)) (φ : (κ → R) → ℂ) (x : κ' → R) :
    GlobalTheory.WeilM.schr ψ w (fun u : κ' → R => φ (u ∘ σ)) x =
      GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) φ (x ∘ σ) := by
  have hd : ∀ u v : κ' → R, (u ∘ σ) ⬝ᵥ (v ∘ σ) = u ⬝ᵥ v := fun u v =>
    Equiv.sum_comp σ fun i => u i * v i
  simp only [GlobalTheory.WeilM.schr, hd]
  rfl

theorem thetaSum_reindex (F : Type) [Field F] [NumberField F] {κ κ' : Type} (σ : κ ≃ κ')
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (fun u : κ' → AdeleRing (𝓞 F) F => Φ (u ∘ σ)) = GlobalTheory.WeilM.thetaSum F Φ := by
  unfold GlobalTheory.WeilM.thetaSum
  exact (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq
    (fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))

theorem theta_transform_injOn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  intro D ψ hψ κ _ Φ hΦ Φ' hΦ' h
  classical
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have key : ∀ (Ψ : (κ → AF D.host.F) → ℂ) (w : GlobalTheory.ThetaTransform.VA D.host.F (Fintype.card κ)),
      GlobalTheory.ThetaTransform.thV ψ (fun u : Fin (Fintype.card κ) → AF D.host.F => Ψ (u ∘ σ)) w =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ) := by
    intro Ψ w
    rw [← thetaSum_reindex D.host.F σ (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ)]
    unfold GlobalTheory.ThetaTransform.thV
    congr 1
    funext x
    exact schr_reindex ψ σ w Ψ x
  have e := GlobalTheory.ThetaTransform.thV_injOn hR hψ.1 (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ)
    (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ') (funext fun w => by rw [key, key]; exact h _)
  funext x
  have := congrFun e (x ∘ σ.symm)
  simpa [Function.comp_assoc] using this

end GlobalTheory.CompanionTheory.ThetaInj

end

end ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | exact ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | (intros; apply ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn <;> assumption)

end
