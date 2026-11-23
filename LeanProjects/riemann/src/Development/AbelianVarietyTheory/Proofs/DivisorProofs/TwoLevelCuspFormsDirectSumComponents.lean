import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

def onComp (M : TwoLevels E r U C) (c : C) : Submodule ℂ (C → M.dom → ℂ) where
  carrier := {v | ∀ c', c' ≠ c → v c' = 0}
  add_mem' := by
    intro a b ha hb c' hc
    simp [ha c' hc, hb c' hc]
  zero_mem' := by
    intro c' _
    rfl
  smul_mem' := by
    intro t a ha c' hc
    simp [ha c' hc]

def cut (M : TwoLevels E r U C) (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] (C → M.dom → ℂ) where
  toFun v := fun c' => if c' = c then v c' else 0
  map_add' := by
    intro a b
    funext c' x
    by_cases h : c' = c <;> simp [h]
  map_smul' := by
    intro t a
    funext c' x
    by_cases h : c' = c <;> simp [h]

theorem cut_apply (M : TwoLevels E r U C) (c : C) (v : C → M.dom → ℂ) (c' : C) :
    cut M c v c' = if c' = c then v c' else 0 := rfl

theorem cutF_mem_SS (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {F : C → Frame M.Ψ r → ℂ}
    (hF : F ∈ M.SS la) : (fun c' => if c' = c then F c' else 0) ∈ M.SS la := by
  intro c'
  by_cases h : c' = c
  · simpa [h] using hF c'
  · simp only [h, if_false]
    exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem cut_mem_cusp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) : cut M c v ∈ M.cusp la := by
  have : (M.cusp la).map (cut M c) ≤ M.cusp la := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, cutF_mem_SS M la c hF, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

theorem mem_span_of_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) (hc : v ∈ onComp M c) :
    v ∈ Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
  have hcut : cut M c v = v := by
    funext c' x
    by_cases h : c' = c
    · simp [cut_apply, h]
    · simp [cut_apply, h, hc c' h]
  rw [← hcut]
  have : (M.cusp la).map (cut M c) ≤
      Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨cutF_mem_SS M la c hF, fun c' hc' => by simp [hc']⟩, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

end GlobalTheory.ShareOn.Decomp

end

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

theorem pullRep_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la))
    (hρ : IsPullRep M la ρ) (g : U) (c : C) (w : M.cusp la) (hw : (w : C → M.dom → ℂ) ∈ onComp M c) :
    ((ρ g⁻¹ w : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨w, hwc⟩ := w
  have hs := mem_span_of_onComp M la c hwc hw
  clear hw
  revert hwc
  suffices H : ∀ h' : w ∈ M.cusp la, ((ρ g⁻¹ ⟨w, h'⟩ : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) from fun h' => H h'
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, ⟨hF, hFc⟩, rfl⟩ := hy
    intro h' c' hc'
    funext x
    have hgc : g • c' ≠ c := fun h => hc' (eq_inv_smul_iff.2 h)
    have := ha g F hF c' x
    rw [this]
    simp [TwoLevels.pull, hFc _ hgc]
  | zero =>
    intro h'
    have : (⟨0, h'⟩ : M.cusp la) = 0 := rfl
    rw [this, map_zero]
    exact (onComp M (g⁻¹ • c)).zero_mem
  | add x y hx hy ihx ihy =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have hy' : y ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hy
    have : (⟨x + y, h'⟩ : M.cusp la) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add, Submodule.coe_add]
    exact (onComp M (g⁻¹ • c)).add_mem (ihx hx') (ihy hy')
  | smul t x hx ihx =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have : (⟨t • x, h'⟩ : M.cusp la) = t • ⟨x, hx'⟩ := rfl
    rw [this, map_smul, Submodule.coe_smul]
    exact (onComp M (g⁻¹ • c)).smul_mem t (ihx hx')

end GlobalTheory.ShareOn.Decomp

open GlobalTheory.ShareOn.Decomp in

theorem GlobalTheory.ShareOn.cusp_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C]
    [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧
      ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ
  have : Fintype C := Fintype.ofFinite C
  refine ⟨fun c => (onComp M c).comap (M.cusp ka).subtype, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro x hx hx2
      have hle : (⨆ j, ⨆ (_ : j ≠ i), (onComp M j).comap (M.cusp ka).subtype) ≤
          LinearMap.ker ((LinearMap.proj i : (C → M.dom → ℂ) →ₗ[ℂ] (M.dom → ℂ)) ∘ₗ (M.cusp ka).subtype) := by
        refine iSup₂_le fun j hj => ?_
        intro y hy
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype]
        exact hy i (Ne.symm hj)
      have h0 := hle hx2
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype] at h0
      apply Subtype.ext
      funext c'
      by_cases h : c' = i
      · subst h; simpa using h0
      · simpa using hx c' h
    · rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      have hsum : (⟨v, hv⟩ : M.cusp ka) = ∑ c, ⟨GlobalTheory.ShareOn.Decomp.cut M c v, cut_mem_cusp M ka c hv⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext c' x
        simp only [Finset.sum_apply, GlobalTheory.ShareOn.Decomp.cut_apply]
        have hh : ∀ c, (if c' = c then v c' else 0) x = if c' = c then v c' x else 0 := fun c => by
          split_ifs <;> rfl
        simp only [hh]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsum]
      refine Submodule.sum_mem_iSup fun c => ?_
      intro c' hc'
      simp [GlobalTheory.ShareOn.Decomp.cut_apply, hc']
  · intro h c v hv
    have := pullRep_onComp M ka ρ hρ h⁻¹ c v hv
    simp only [inv_inv] at this
    exact this
