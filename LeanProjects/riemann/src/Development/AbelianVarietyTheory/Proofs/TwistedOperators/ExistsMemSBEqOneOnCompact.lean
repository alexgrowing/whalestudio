import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem exists_mem_SB_eq_one_on_compact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (C : Set (n → k)) (hC : IsCompact C) :
    ∃ χ ∈ SB (n → k), ∀ u ∈ C, χ u = 1 := by
  classical
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  let B : Set (n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hc
  let U : (n → k) → Set (n → k) := fun x => (Homeomorph.addLeft x) '' B
  have hUo : ∀ x, IsOpen (U x) := fun x => (Homeomorph.addLeft x).isOpenMap _ hBo
  have hUc : ∀ x, IsCompact (U x) := fun x => hBc.image (Homeomorph.addLeft x).continuous
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUo fun x _ =>
    Set.mem_iUnion.mpr ⟨x, 0, fun _ _ => zero_mem _, by simp⟩
  set K : Set (n → k) := ⋃ x ∈ t, U x with hK
  have hKo : IsOpen K := isOpen_biUnion fun x _ => hUo x
  have hKc : IsCompact K := t.isCompact_biUnion fun x _ => hUc x
  have hcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  refine ⟨K.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, fun u hu => Set.indicator_of_mem (ht hu) _⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.RootEx
