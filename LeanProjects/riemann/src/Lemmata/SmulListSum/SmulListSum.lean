import Mathlib

universe u_1

namespace Bl.SmulListSum

private theorem smul_list_sum {U : Type u_1} [AddCommGroup U] [Module Complex U]
    (c : Complex) (l : List U) : c • l.sum = (l.map (fun w => c • w)).sum := by
  induction l with
  | nil => simp only [List.sum_nil, List.map_nil, smul_zero]
  | cons a t ih => simp only [List.sum_cons, List.map_cons, smul_add, ih]

theorem goal1 :
  ∀ {U : Type u_1} [inst : AddCommGroup.{u_1} U] [inst_1 : Module.{0, u_1} Complex U] {G : Set.{u_1} U},
  (∀ (w : U),
      Membership.mem.{u_1, u_1} G w → ∀ (c : Complex), Membership.mem.{u_1, u_1} G (HSMul.hSMul.{0, u_1, u_1} c w)) →
    ∀ {y : U},
      Membership.mem.{u_1, u_1} (Submodule.span.{0, u_1} Complex G) y →
        Exists.{u_1 + 1} fun (l : List.{u_1} U) ↦
          And (∀ (w : U), Membership.mem.{u_1, u_1} l w → Membership.mem.{u_1, u_1} G w)
            (Eq.{u_1 + 1} y (List.sum.{u_1} l)) := by
  intro U _ _ G hG y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    refine ⟨[x], ?_, ?_⟩
    · intro w hw
      rw [List.mem_singleton] at hw
      rw [hw]; exact hx
    · simp only [List.sum_cons, List.sum_nil, add_zero]
  | zero => exact ⟨[], fun w hw => absurd hw (List.not_mem_nil), by simp only [List.sum_nil]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨la, hla, rfl⟩ := iha
    obtain ⟨lb, hlb, rfl⟩ := ihb
    refine ⟨la ++ lb, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact hla w h
      · exact hlb w h
    · rw [List.sum_append]
  | smul c a _ iha =>
    obtain ⟨la, hla, rfl⟩ := iha
    refine ⟨la.map (fun w => c • w), ?_, smul_list_sum c la⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact hG v (hla v hv) c

end Bl.SmulListSum
