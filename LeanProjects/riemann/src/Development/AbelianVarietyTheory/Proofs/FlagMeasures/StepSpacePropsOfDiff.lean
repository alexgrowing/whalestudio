import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepSpaceProps

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

theorem stepSpace_props_of_diff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → (∀ P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) → ∀ P : ℕ, IsKStableOn ε σ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X w) (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w) 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ (P + 1)) ∧ ∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ w' ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (w + c • w') = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w + c • GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w' := by
  intro n ε H _ _ _ σ lam hU hd P
  have hσ : IsCRepOn (UJset ε) σ := hU.1
  refine ⟨?_, fun X hX w hw => ⟨(hd P w hw X hX).hasDerivAt, ?_⟩,
    fun X hX w hw w' hw' c => dAct_add_smul (hd P w hw X hX) (hd P w' hw' X hX) c⟩
  · intro g hg v hv
    have : stepSpace ε lam σ P ≤ (stepSpace ε lam σ P).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, u, hl, hX, hu, rfl⟩
      change σ g (dWord σ l u) ∈ stepSpace ε lam σ P
      rw [dWord_conj hσ hd hg hu l hX]
      refine dWord_mem (by simpa using hl) ?_ (lowKSub_stable ε lam σ g hg u hu)
      intro Y hY
      obtain ⟨X, hXl, rfl⟩ := List.mem_map.mp hY
      exact inG_conj hg (hX X hXl)
    exact this hv
  · induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, u, hl, hl', hu, rfl⟩ := hv
      refine dWord_mem (l := X :: l) (by simpa using hl) ?_ hu
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | h
      · exact hX
      · exact hl' Y h
    | zero => rw [dAct_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have := dAct_add_smul (hd P x hx X hX) (hd P y hy X hX) 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have := dAct_add_smul (hd P 0 (Submodule.zero_mem _) X hX) (hd P x hx X hX) c
      rw [zero_add, dAct_zero, zero_add] at this
      rw [this]
      exact Submodule.smul_mem _ c ihx

end GlobalTheory.StepLoc
