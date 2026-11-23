import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem cone_cycle_isBoundary : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) →
    ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  classical
  intro V F G x hx p c hc hbd
  let cone : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)
  have hcone : ∀ l : List V, cone (Finsupp.single l 1) = Finsupp.single (x :: l) 1 := by
    intro l
    simp [cone, Finsupp.mapDomain_single]
  have hs : ∀ l : List V, bd V (cone (Finsupp.single l 1)) =
      Finsupp.single l 1 - cone (bd V (Finsupp.single l 1)) := by
    intro l
    rw [hcone]
    simp only [bd, Finsupp.linearCombination_single, one_smul, List.length_cons,
      Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_zero,
      map_sum, map_zsmul, hcone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    abel
  have key : ∀ d : List V →₀ ℤ, bd V (cone d) = d - cone (bd V d) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add, map_add, hf, hg, map_add, map_add]
      abel
    | single l n =>
      rw [← Finsupp.smul_single_one]
      simp only [map_zsmul, hs, smul_sub]
  refine ⟨cone c, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    have hl' := Finsupp.mapDomain_support hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl'
    have hm' := (Finsupp.mem_supported _ _).mp hc hm
    exact ⟨hx m hm'.1, by simp [hm'.2]⟩
  · rw [key, hbd, map_zero, sub_zero]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_cycle_bounded_by_cone : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) → ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  first
  | exact @GlobalTheory.cone_cycle_isBoundary
end
