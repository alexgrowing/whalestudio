import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelMoves

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

theorem linear_extension_holds : ExtendLin := by
  intro k _ M T _ _ _ _ ι f g hfg
  classical
  let φ := Finsupp.linearCombination k f
  let ψ := Finsupp.linearCombination k g
  have hle : LinearMap.ker φ ≤ LinearMap.ker ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    simp only [φ, ψ, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    exact hfg c.support c hc
  let φ' := (LinearMap.ker φ).liftQ φ le_rfl
  let ψ' := (LinearMap.ker φ).liftQ ψ hle
  have hinj : LinearMap.ker φ' = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    exact le_rfl
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ' hinj
  refine ⟨ψ'.comp L, fun i => ?_⟩
  have hfi : f i = φ' (Submodule.Quotient.mk (Finsupp.single i 1)) := by
    simp [φ', φ, Finsupp.linearCombination_single]
  have h2 : L (φ' (Submodule.Quotient.mk (Finsupp.single i 1))) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  rw [LinearMap.comp_apply, hfi, h2]
  simp [ψ', ψ, Finsupp.linearCombination_single]

end Formalism.L2.PairingIndexBounds.Mv
