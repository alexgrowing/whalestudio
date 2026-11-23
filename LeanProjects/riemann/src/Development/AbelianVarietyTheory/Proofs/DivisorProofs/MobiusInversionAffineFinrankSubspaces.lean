import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIco

namespace GlobalTheory.CuspGL

theorem finsum_le_oneValue_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A : Submodule K U) :
    ∑ᶠ B : {B : Submodule K U // B ≤ A}, oneValue (Nat.card K) (Module.finrank K B.1) =
      (Module.finrank K A : ℂ) := by
  classical
  haveI : Finite A := Module.finite_of_finite K
  haveI : Fintype (Submodule K A) := Fintype.ofFinite _
  rw [← sum_oneValue_finrank K A, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (Submodule.MapSubtype.orderIso A).toEquiv]
  refine finsum_congr fun W => ?_
  congr 1
  exact Submodule.finrank_map_subtype_eq A W

theorem eq_of_finsum_le_eq {α : Type} [PartialOrder α] [Finite α] (G H : α → ℂ)
    (h : ∀ A : α, ∑ᶠ B : {B : α // B ≤ A}, G B.1 = ∑ᶠ B : {B : α // B ≤ A}, H B.1) (A : α) :
    G A = H A := by
  classical
  induction A using WellFoundedLT.induction with
  | ind A ih =>
    haveI : Fintype {B : α // B ≤ A} := Fintype.ofFinite _
    have h1 := h A
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A})),
      ← Finset.add_sum_erase _ (fun B : {B : α // B ≤ A} => H B.1)
        (Finset.mem_univ (⟨A, le_rfl⟩ : {B : α // B ≤ A}))] at h1
    have h2 : ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), G B.1 =
        ∑ B ∈ Finset.univ.erase (⟨A, le_rfl⟩ : {B : α // B ≤ A}), H B.1 := by
      refine Finset.sum_congr rfl fun B hB => ih B.1 (lt_of_le_of_ne B.2 fun e => ?_)
      exact (Finset.mem_erase.1 hB).1 (Subtype.ext e)
    rw [h2] at h1
    exact add_right_cancel h1

theorem moebius_affine_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ) (hU : 0 < Module.finrank K U)
    (hG : ∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 =
      c₀ + c * (Module.finrank K A : ℂ)) :
    G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by
  classical
  haveI : Finite U := Module.finite_of_finite K
  have key := eq_of_finsum_le_eq G
    (fun B => (if B = ⊥ then c₀ else 0) + c * oneValue (Nat.card K) (Module.finrank K B)) (fun A => by
      haveI : Fintype {B : Submodule K U // B ≤ A} := Fintype.ofFinite _
      rw [hG A, ← finsum_le_oneValue_finrank K U A, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_eq_single (⟨⊥, bot_le⟩ : {B : Submodule K U // B ≤ A})]
      · simp
      · intro B _ hB
        exact if_neg fun e => hB (Subtype.ext e)
      · intro h
        exact absurd (Finset.mem_univ _) h) ⊤
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos hU
  rw [key, if_neg top_ne_bot, zero_add, finrank_top, oneValue, if_neg hU.ne']

end GlobalTheory.CuspGL
