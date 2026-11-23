import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEv.PartLTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def reindexFun {R : Type} {ι ι' : Type} (e : ι ≃ ι') : ((ι → R) → ℂ) →ₗ[ℂ] ((ι' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun y : ι' → R => y ∘ e)

theorem reindexFun_apply {R : Type} {ι ι' : Type} (e : ι ≃ ι') (Φ : (ι → R) → ℂ) (y : ι' → R) :
    reindexFun e Φ y = Φ (y ∘ e) := rfl

theorem isTame_reindexFun {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    IsTame F (reindexFun (R := AF F) e) := by
  intro g hg
  let L : (ι' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (ι → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e).toContinuousLinearEquiv
  let H : (ι' → FiniteAdeleRing (𝓞 F) F) ≃ₜ (ι → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun y => y ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := fun y => by funext i; simp
      right_inv := fun z => by funext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply (e i)
      continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i) }
  refine ⟨Unit, inferInstance, fun _ => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun _ => g ∘ H,
    fun _ => ⟨hg.1.comp_continuous H.continuous, hg.2.comp_homeomorph H⟩, fun f => ?_⟩
  funext y
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem isTame_partL : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  intro F _ _ κ κ₁ κ' _ _ _ T hT
  have h : partL (κ' := κ') T = reindexFun (Equiv.sumComm κ' κ₁) ∘ₗ partR (κ := κ') T ∘ₗ
      reindexFun (Equiv.sumComm κ κ') := by
    refine LinearMap.ext fun Φ => funext fun s => ?_
    simp only [LinearMap.comp_apply, reindexFun_apply, partR_apply, partL_apply]
    exact congrArg₂ (fun φ t => T φ t) (funext fun x => congrArg Φ (funext fun i => by cases i <;> rfl)) rfl
  rw [h]
  exact ((isTame_reindexFun _).comp (GlobalTheory.T.tame_part_right F κ' κ κ₁ T hT)).comp (isTame_reindexFun _)

end GlobalTheory.DoublingEv.PartLTame
