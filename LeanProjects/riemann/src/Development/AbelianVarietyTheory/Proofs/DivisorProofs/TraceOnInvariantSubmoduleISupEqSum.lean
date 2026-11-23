import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dif_pos hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dif_pos (hinv i)]

end GlobalTheory.BCT
