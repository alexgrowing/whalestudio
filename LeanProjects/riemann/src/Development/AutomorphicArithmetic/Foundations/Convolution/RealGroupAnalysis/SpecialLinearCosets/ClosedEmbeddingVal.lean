import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem trace_compactOpen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    {C : Set Y} (hCo : IsOpen C) (hCc : IsCompact C) :
    ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = C := by
  have hcl : IsClosed (i '' Cᶜ) := hi.isClosedMap _ hCo.isClosed_compl
  have hloc : ∀ y ∈ C, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i y ∈ O ∧ O ⊆ (i '' Cᶜ)ᶜ := by
    intro y hy
    refine hb (i y) _ (hcl.isOpen_compl.mem_nhds ?_)
    rintro ⟨y', hy', e⟩
    exact hy' (hi.injective e ▸ hy)
  choose! O hOo hOc hOy hON using hloc
  obtain ⟨t, ht, hcov⟩ := hCc.elim_nhds_subcover (fun y => i ⁻¹' O y)
    (fun y hy => ((hOo y hy).preimage hi.continuous).mem_nhds (hOy y hy))
  refine ⟨⋃ y ∈ t, O y, isOpen_biUnion fun y hy => hOo y (ht y hy),
    t.isCompact_biUnion fun y hy => hOc y (ht y hy), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hz, hy⟩
    by_contra hc
    exact hON z (ht z hz) hy ⟨y, hc, rfl⟩
  · intro hy
    simpa using hcov hy

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {O : Set X}
    (hO : IsOpen O) (hc : IsCompact O) : O.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ O
  · exact ⟨O, hO, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Oᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem extend_SB {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsClosedEmbedding i)
    (hb : ∀ x, ∀ N ∈ 𝓝 x, ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N)
    (a : Y → ℂ) (ha : a ∈ SB Y) : ∃ b ∈ SB X, ∀ y, b (i y) = a y := by
  obtain ⟨hlc, hcs⟩ := ha
  have hK : IsCompact (tsupport a) := hcs
  haveI : CompactSpace (tsupport a) := isCompact_iff_compactSpace.mp hK
  have hfin : (Set.range ((tsupport a).restrict a)).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hfib : ∀ c : ℂ, c ≠ 0 → ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ i ⁻¹' O = a ⁻¹' {c} := by
    intro c hc
    refine trace_compactOpen hi hb (hlc.isOpen_fiber c) (hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_)
    intro y hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support, show a y = c from hy]
    exact hc
  choose! O hOo hOc hOt using hfib
  let S : Finset ℂ := hfin.toFinset.erase 0
  refine ⟨fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x, ?_, ?_⟩
  · have : (fun x => ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) x) =
        ∑ c ∈ S, c • (O c).indicator (fun _ => (1 : ℂ)) := by
      ext x
      simp [Finset.sum_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    exact indicator_mem_SB (hOo c hc0) (hOc c hc0)
  · intro y
    have hterm : ∀ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = if c = a y then c else 0 := by
      intro c hc
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hm : i y ∈ O c ↔ a y = c := by
        have := Set.ext_iff.mp (hOt c hc0) y
        simpa using this
      by_cases h : c = a y
      · rw [Set.indicator_of_mem (hm.mpr h.symm), if_pos h, mul_one]
      · have : i y ∉ O c := fun h' => h (hm.mp h').symm
        rw [Set.indicator_of_notMem this, if_neg h, mul_zero]
    change ∑ c ∈ S, c * (O c).indicator (fun _ => (1 : ℂ)) (i y) = a y
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S (a y) (fun c => c)]
    split_ifs with h
    · rfl
    · have h0 : a y = 0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr ⟨⟨y, subset_tsupport _ hne⟩, rfl⟩⟩)
      exact h0.symm

private theorem closedEmbedding_val (F : Type) [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (Subtype.val : SL v → M2 v) := by
  refine IsClosed.isClosedEmbedding_subtypeVal ?_
  exact isClosed_singleton.preimage (continuous_id.matrix_det)

private theorem compactOpen_basis (F : Type) [Field F] [NumberField F] (v : P F) (x : M2 v) (N : Set (M2 v))
    (hN : N ∈ 𝓝 x) : ∃ O : Set (M2 v), IsOpen O ∧ IsCompact O ∧ x ∈ O ∧ O ⊆ N := by
  have h0 : (fun y : M2 v => x + y) ⁻¹' N ∈ 𝓝 (0 : M2 v) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨U, hUo, hUc, hUN⟩ := (UpperTheory.ConvolutionTheory.R2.I.lgrp F v).2
    ((fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) ⁻¹' ((fun y : M2 v => x + y) ⁻¹' N))
    (by
      have : Tendsto (fun y : Multiplicative (M2 v) => Multiplicative.toAdd y) (𝓝 1) (𝓝 (0 : M2 v)) :=
        continuous_toAdd.tendsto _
      exact this h0)
  let e : Multiplicative (M2 v) → M2 v := fun y => x + Multiplicative.toAdd y
  have he : IsOpenEmbedding e := (Homeomorph.addLeft x).isOpenEmbedding
  refine ⟨e '' U, he.isOpenMap _ hUo, hUc.image he.continuous, ⟨1, U.one_mem, by simp [e]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hUN hy

theorem UpperTheory.ConvolutionTheory.R2.I.ext :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : SB (SL v)), ∃ b : SB (M2 v), ∀ m : SL v, b.1 m.1 = a.1 m := by
  intro F _ _ v a
  obtain ⟨b, hb, h⟩ := extend_SB (closedEmbedding_val F v) (compactOpen_basis F v) a.1 a.2
  exact ⟨⟨b, hb⟩, h⟩
