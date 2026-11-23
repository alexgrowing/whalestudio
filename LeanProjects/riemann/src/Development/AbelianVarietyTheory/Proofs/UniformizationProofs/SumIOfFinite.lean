import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

namespace GlobalTheory.UT

theorem sumI_of_finite {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E)
    (S : Finset Ix) (hS : ∀ i, i ∉ S → x i = 0) : SumI I x (∑ i ∈ S, x i) := by
  classical
  have hx : ∀ i, x i ∈ Submodule.span R (↑(S.image x) : Set E) := fun i => by
    by_cases h : i ∈ S
    · exact Submodule.subset_span (by simpa using ⟨i, h, rfl⟩)
    · rw [hS i h]; exact Submodule.zero_mem _
  refine ⟨Submodule.span R ↑(S.image x), ⟨_, rfl⟩, Submodule.sum_mem _ fun i _ => hx i, hx, fun n => ⟨S, fun T hT => ?_⟩⟩
  rw [Finset.sum_subset hT (fun i _ h => hS i h), sub_self]; exact Submodule.zero_mem _

end GlobalTheory.UT
