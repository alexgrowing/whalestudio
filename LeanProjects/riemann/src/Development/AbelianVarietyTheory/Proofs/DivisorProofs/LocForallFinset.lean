import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.LocalizedFinsetForAll

theorem loc_forall_finset {U : Scheme.{0}} {ι : Type u} (s : Finset ι)
    {P : ι → (V : Scheme.{0}) → (V ⟶ U) → Prop} (h : ∀ i ∈ s, GlobalTheory.EtC.Loc U (P i)) :
    GlobalTheory.EtC.Loc U fun (V : Scheme.{0}) (g : V ⟶ U) ↦ ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨S, hS, hSP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨T, hT, hTP⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨S ⊓ T, GrothendieckTopology.intersection_covering _ hS hT, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hSP V g hg.1
    · exact hTP V g hg.2 i hi

end GlobalTheory.LocalizedFinsetForAll
