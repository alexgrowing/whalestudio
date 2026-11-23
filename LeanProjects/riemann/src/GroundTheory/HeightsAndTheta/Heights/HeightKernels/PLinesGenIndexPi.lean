import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexPi

open AddSubgroup

variable {η : Type} {G : Type} [AddCommGroup G]

theorem index_pi_dep [Fintype η] {β : η → Type} [∀ i, AddCommGroup (β i)]
    (H : ∀ i, AddSubgroup (β i)) :
    (AddSubgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

def piIncl (K : η → AddSubgroup G) : (∀ i, K i) →+ AddSubgroup.pi Set.univ K where
  toFun x := ⟨fun i => (x i : G), by simp [AddSubgroup.mem_pi]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem piIncl_surjective (K : η → AddSubgroup G) : Function.Surjective (piIncl K) := by
  intro y
  refine ⟨fun i => ⟨(y : η → G) i, (AddSubgroup.mem_pi _).1 y.2 i (Set.mem_univ i)⟩, ?_⟩
  rfl

theorem relIndex_pi [Fintype η] (H K : η → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) =
      ∏ i, (H i).relIndex (K i) := by
  have hc : ((AddSubgroup.pi Set.univ H).addSubgroupOf (AddSubgroup.pi Set.univ K)).comap
      (piIncl K) = AddSubgroup.pi Set.univ fun i => (H i).addSubgroupOf (K i) := by
    ext x
    simp [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi, piIncl]
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ (piIncl_surjective K), hc, index_pi_dep]

end KLinesGenIndexPi

theorem LinesGenIndexPi.proof : LinesGenIndexPi.Statement := by
  intro η _ G _ A B
  unfold genIndex
  rw [KLinesGenIndexPi.relIndex_pi, KLinesGenIndexPi.relIndex_pi, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]

end GroundTheory.Heights₂.Heights
