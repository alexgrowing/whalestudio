import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

noncomputable section

open Classical

namespace GlobalTheory.SeqCx

namespace DblRow

variable {V W : Type}

theorem pair_injective (w : List W) : Function.Injective (fun l : List V => (l, w)) :=
  fun _ _ h => (Prod.mk.inj h).1

def proj (w : List W) (x : List V × List W →₀ ℤ) : List V →₀ ℤ :=
  Finsupp.comapDomain (fun l : List V => (l, w)) x (pair_injective w).injOn

theorem proj_apply (w : List W) (x : List V × List W →₀ ℤ) (l : List V) :
    proj w x l = x (l, w) := rfl

def incl (w : List W) : (List V →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => (l, w))

theorem incl_apply (w w' : List W) (z : List V →₀ ℤ) (l : List V) :
    incl w z (l, w') = if w = w' then z l else 0 := by
  by_cases h : w = w'
  · subst h
    rw [if_pos rfl]
    exact Finsupp.mapDomain_apply (pair_injective w) z l
  · rw [if_neg h]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact h (congrArg Prod.snd hl')

theorem hbd_incl (w : List W) (z : List V →₀ ℤ) : hbd V W (incl w z) = incl w (bd V z) := by
  have : (hbd V W).comp (incl w) = (incl w).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l c
    simp only [LinearMap.comp_apply]
    rw [show Finsupp.single l c = c • Finsupp.single l (1 : ℤ) by simp, map_smul, map_smul, map_smul,
      map_smul]
    congr 1
    simp only [incl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hbd,
      Finsupp.linearCombination_single, one_smul]
  exact LinearMap.congr_fun this z

theorem decomp (x : List V × List W →₀ ℤ) :
    x = ∑ w ∈ x.support.image Prod.snd, incl w (proj w x) := by
  ext ⟨l, w'⟩
  rw [Finsupp.finset_sum_apply]
  simp only [incl_apply, proj_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (Finset.mem_image.2 ⟨(l, w'), Finsupp.mem_support_iff.2 (Ne.symm hne), rfl⟩)

end DblRow

open DblRow

theorem dblRow_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ),
    (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) →
    ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  intro V W D a b hex x hx h0
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  set T := x.support.image Prod.snd with hT
  have h1 : hbd V W x = ∑ w ∈ T, incl w (bd V (proj w x)) := by
    conv_lhs => rw [decomp x]
    rw [map_sum]
    simp only [hbd_incl]
    rfl
  have hbd0 : ∀ w ∈ T, bd V (proj w x) = 0 := by
    intro w hw
    ext l
    have := congrArg (fun z => z (l, w)) h1
    simp only [h0, Finsupp.coe_zero, Pi.zero_apply, Finsupp.finset_sum_apply, incl_apply] at this
    rw [Finset.sum_ite_eq', if_pos hw] at this
    simpa using this.symm
  have hslice : ∀ w ∈ T, ∃ y ∈ chains {l | (l, w) ∈ D} (a + 1), bd V y = proj w x := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hzD, -, hzb⟩ := hsupp z hz
    refine hex z.2 hzb ⟨z.1, hzD⟩ (proj z.2 x) ?_ (hbd0 z.2 hw)
    intro l hl
    have hl' : (l, z.2) ∈ x.support := by
      have hl2 := Finset.mem_coe.1 hl
      rw [Finsupp.mem_support_iff] at hl2 ⊢
      exact hl2
    obtain ⟨h2, h3, -⟩ := hsupp _ hl'
    exact ⟨h2, h3⟩
  choose! yw hyw hywb using hslice
  refine ⟨∑ w ∈ T, incl w (yw w), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun w hw => ?_
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨h2, h3⟩ := hyw w hw hl
    obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨h2, h3, (hsupp z0 hz0).2.2⟩
  · rw [map_sum]
    simp only [hbd_incl]
    conv_rhs => rw [decomp x]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hywb w hw]

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqHorizontalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) → ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.dblRow_exact
  | exact @GlobalTheory.SeqCx.DblRow.decomp
  | exact @GlobalTheory.SeqCx.DblRow.hbd_incl
  | exact @GlobalTheory.SeqCx.DblRow.incl_apply
  | exact @GlobalTheory.SeqCx.DblRow.proj_apply
  | exact @GlobalTheory.SeqCx.DblRow.pair_injective
end
