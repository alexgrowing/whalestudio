import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.BlockSwap

section Generic

variable {A : Type} {κ κ' κ₁' : Type}

def swapV (z : κ' ⊕ κ → A) : κ ⊕ κ' → A := z ∘ Sum.swap

theorem partR_eq_partL_swap (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) (y : κ ⊕ κ₁' → A) :
    partR T Φ y = partL T (fun z : κ' ⊕ κ → A => Φ (swapV z)) (swapV y) := by
  simp only [partR, partL, swapV]
  congr 1
  funext x
  congr 1
  funext i
  cases i <;> rfl

end Generic

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def swapCLE (M : Type) [NormedAddCommGroup M] [NormedSpace ℝ M] (κ κ' : Type) : (κ' ⊕ κ → M) ≃L[ℝ] (κ ⊕ κ' → M) :=
  { LinearEquiv.funCongrLeft ℝ M (Equiv.sumComm κ κ') with
    continuous_toFun := continuous_pi fun _ => continuous_apply _
    continuous_invFun := continuous_pi fun _ => continuous_apply _ }

def swapH (X : Type) [TopologicalSpace X] (κ κ' : Type) : (κ' ⊕ κ → X) ≃ₜ (κ ⊕ κ' → X) where
  toFun := swapV
  invFun := swapV
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by funext i; cases i <;> rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem sb_swap {X : Type} [TopologicalSpace X] {κ κ' : Type} {g : (κ ⊕ κ' → X) → ℂ} (hg : g ∈ SB (κ ⊕ κ' → X)) :
    (fun z : κ' ⊕ κ → X => g (swapV z)) ∈ SB (κ' ⊕ κ → X) :=
  ⟨hg.1.comp_continuous (swapH X κ κ').continuous, hg.2.comp_homeomorph (swapH X κ κ')⟩

theorem partR_of_partL {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ)
    (hL : ∃ P : SInf F (κ' ⊕ κ) →L[ℂ] SInf F (κ₁' ⊕ κ), ∀ g ∈ SB (κ' ⊕ κ → Af F), ∃ g₁ ∈ SB (κ₁' ⊕ κ → Af F),
      ∀ f : SInf F (κ' ⊕ κ), partL e (pureA F f g) = pureA F (P f) g₁) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  obtain ⟨PL, hPL⟩ := hL
  refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ₁' κ)).comp
    (PL.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ'))), fun g hg => ?_⟩
  obtain ⟨g₁, hg₁, h⟩ := hPL _ (sb_swap hg)
  refine ⟨fun w => g₁ (swapV w), sb_swap hg₁, fun f => ?_⟩
  funext y
  rw [partR_eq_partL_swap]
  have hpure : (fun z : κ' ⊕ κ → AF F => pureA F (⇑f) g (swapV z)) =
      pureA F (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ') f)) (fun w => g (swapV w)) := rfl
  rw [hpure, h]
  rfl

end Adelic

end GlobalTheory.DblEval.BlockSwap

end
