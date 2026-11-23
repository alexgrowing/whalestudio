import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in

theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (H := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩

open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in

theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

theorem exists_extension : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (U Z : Set X), IsOpen U → Z ⊆ U → ∀ f : SB Z, ∃ F : SB X, (∀ z : Z, F.1 z = f.1 z) ∧ ∀ x, x ∉ U → F.1 x = 0 := by
  classical
  intro X _ _ _ _ U Z hU hZU f
  obtain ⟨f, hl, hs⟩ := f
  have hfin : (f '' tsupport f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hs
    have := (hl.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
    refine this.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have h : ∀ c : ℂ, ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ V ⊆ U ∧
      (c ≠ 0 → ∀ z : Z, (z : X) ∈ V ↔ f z = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isClopen_empty, Set.empty_subset _, fun h => absurd hc h⟩
    have hcl := hl.isClopen_fiber c
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 hcl.isOpen
    have hcomp : IsCompact {z : Z | f z = c} :=
      hs.isCompact.of_isClosed_subset hcl.isClosed fun z hz =>
        subset_tsupport _ (by
          rw [Function.mem_support, show f z = c from hz]; exact hc)
    obtain ⟨V, hV1, hV2, hV3, hV4⟩ := exists_isCompact_isClopen_between
      (hcomp.image continuous_subtype_val) (hW.inter hU) (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨(hWe.symm ▸ hz : z ∈ Subtype.val ⁻¹' W), hZU z.2⟩)
    refine ⟨V, hV1, hV2, fun x hx => (hV4 hx).2, fun _ z => ⟨fun hz => ?_, fun hz => hV3 ⟨z, hz, rfl⟩⟩⟩
    have : z ∈ Subtype.val ⁻¹' W := (hV4 hz).1
    rw [hWe] at this
    exact this
  choose V hV1 hV2 hV3 hV4 using h
  refine ⟨⟨∑ c ∈ hfin.toFinset.erase 0, c • (V c).indicator fun _ => (1 : ℂ),
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (indicator_mem_SB (hV1 c) (hV2 c))⟩,
    fun z => ?_, fun x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (f z)]
    · by_cases hz : f z = 0
      · simp [hz]
      · rw [Set.indicator_of_mem ((hV4 _ hz z).2 rfl), mul_one]
    · intro c hc hne
      rw [Set.indicator_of_notMem (fun h => hne ((hV4 c (Finset.ne_of_mem_erase hc) z).1 h).symm),
        mul_zero]
    · intro hn
      by_cases hz : f z = 0
      · simp [hz]
      · exact absurd (Finset.mem_erase.2 ⟨hz, hfin.mem_toFinset.2 ⟨z, subset_tsupport _ hz, rfl⟩⟩) hn
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun c _ => by
      rw [Set.indicator_of_notMem (fun h => hx (hV3 c h)), mul_zero]

end GlobalTheory.SBExtend
