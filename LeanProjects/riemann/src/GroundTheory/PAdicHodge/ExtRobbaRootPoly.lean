import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

theorem nnnorm_multiset_sum_le_of_forall {m : Multiset F} {B : NNReal} (h : ∀ x ∈ m, ‖x‖₊ ≤ B) :
    ‖m.sum‖₊ ≤ B := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem nnnorm_multiset_prod' (m : Multiset F) : ‖m.prod‖₊ = (m.map fun a => ‖a‖₊).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.prod_cons, nnnorm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

variable [IsAlgClosed F]

end GroundTheory.PAdicHodge
