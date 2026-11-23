import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def leftInv : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g}
  zero_mem' _ _ := rfl
  add_mem' {ψ ψ'} h h' γ g := by simp [h γ g, h' γ g]
  smul_mem' c ψ h γ g := by simp [h γ g]

theorem lie_mem_leftInv (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ leftInv E a) : lie E a X ψ ∈ leftInv E a := by
  intro γ g
  have e : chart ψ.1 (ratGL E a γ * g) = chart ψ.1 g := by
    funext x
    simp only [chart, mul_assoc]
    split_ifs
    · exact h γ _
    · rfl
  simp only [lie_apply, lieD, e]

variable (E a) in

def fixL (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ k ∈ L, finRep E a k ψ = ψ}
  zero_mem' k _ := map_zero _
  add_mem' {ψ ψ'} h h' k hk := by rw [map_add, h k hk, h' k hk]
  smul_mem' c ψ h k hk := by rw [map_smul, h k hk]

theorem lie_mem_fixL (L : Subgroup (GL (Fin a) (Af E))) (X : Lie E a) {ψ : Sm E a} (h : ψ ∈ fixL E a L) :
    lie E a X ψ ∈ fixL E a L := by
  intro k hk
  have e := LinearMap.congr_fun (lie_rt_fin X k) ψ
  simp only [Module.End.mul_apply] at e
  change rt E a (finGL E a k) (lie E a X ψ) = lie E a X ψ
  rw [← e]
  exact congrArg (lie E a X) (h k hk)

theorem comp_mem_maps : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  intro E _ _ _ a L W hW T hT z hz
  refine ⟨fun k w => ?_, fun w => ⟨?_, ?_, ?_⟩⟩
  · simp only [LinearMap.comp_apply, hT.1 k w]
    exact (LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E a k z hz) (T w))
  · exact Zalg_stable (V := tame E a) (fun X _ h => lie_mem_tame X h) hz _ (hT.2 w).1
  · exact Zalg_stable (V := leftInv E a) (fun X _ h => lie_mem_leftInv X h) hz _ (hT.2 w).2.1
  · exact Zalg_stable (V := fixL E a L) (fun X _ h => lie_mem_fixL L X h) hz _ (hT.2 w).2.2

end GlobalTheory.AutGrowth
