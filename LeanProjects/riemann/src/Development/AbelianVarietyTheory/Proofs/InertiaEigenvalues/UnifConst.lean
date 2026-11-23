import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TestFn

theorem unif_const (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ)
    (hf : IsTest f) : ∃ V ∈ 𝓝 (0 : X), ∀ x v, v ∈ V → f (x + v) = f x := by
  classical
  have hC : IsCompact (tsupport f) := hf.2
  have hW : ∀ x : X, ∃ W ∈ 𝓝 (0 : X), ∀ w₁ ∈ W, ∀ w₂ ∈ W, f (x + w₁ + w₂) = f x := by
    intro x
    have ho : IsOpen (f ⁻¹' {f x}) := hf.1.isOpen_fiber (f x)
    have hmem : f ⁻¹' {f x} ∈ 𝓝 (x + (0 : X) + 0) := by simpa using ho.mem_nhds (by simp)
    have hcont : Continuous (fun p : X × X => x + p.1 + p.2) := by fun_prop
    have h2 := hcont.continuousAt (x := ((0 : X), (0 : X))) hmem
    rw [nhds_prod_eq] at h2
    obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := Filter.mem_prod_iff.mp h2
    refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, fun w₁ h₁ w₂ h₂ => ?_⟩
    exact hsub (Set.mk_mem_prod h₁.1 h₂.2)
  choose W hW0 hWf using hW
  have hnb : ∀ x ∈ tsupport f, (fun w => x + w) '' W x ∈ 𝓝 x := by
    intro x _
    have h1 : (fun w => x + w) '' W x = (fun y => -x + y) ⁻¹' W x := by
      ext y; constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hy; exact ⟨-x + y, hy, by abel⟩
    rw [h1]
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW0 x)
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover _ hnb
  set V₀ : Set X := ⋂ x ∈ t, W x
  have hV₀ : V₀ ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).mpr fun x _ => hW0 x
  have hcase : ∀ y ∈ tsupport f, ∀ v ∈ V₀, f (y + v) = f y := by
    intro y hy v hv
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    obtain ⟨w, hw, rfl⟩ := hyx
    have hvx : v ∈ W x := Set.mem_iInter₂.mp hv x hxt
    have e1 := hWf x w hw v hvx
    have e2 : f (x + w) = f x := by simpa using hWf x w hw 0 (mem_of_mem_nhds (hW0 x))
    rw [e2, ← e1]
  refine ⟨V₀ ∩ (fun v => -v) ⁻¹' V₀, Filter.inter_mem hV₀ (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV₀)),
    fun x v hv => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hcase x hx v hv.1
  by_cases hxv : x + v ∈ tsupport f
  · have := hcase (x + v) hxv (-v) hv.2
    simp only [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxv]

theorem slice_test {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (T : X × Y → ℂ) (hT : IsTest T) (y : Y) :
    IsTest (fun x => T (x, y)) := by
  refine ⟨hT.1.comp_continuous (Continuous.prodMk_left y), ?_⟩
  have hc : IsCompact (Prod.fst '' tsupport T) := hT.2.image continuous_fst
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  have h1 : IsClosed ((fun x => (x, y)) ⁻¹' tsupport T) := (isClosed_tsupport T).preimage (Continuous.prodMk_left y)
  refine (closure_minimal ?_ h1).trans ?_
  · intro x hx; exact subset_tsupport T hx
  · intro x hx; exact ⟨(x, y), hx, rfl⟩

end GlobalTheory.TestFn
