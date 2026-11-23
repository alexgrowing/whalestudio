import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree

noncomputable section

namespace RootFieldNumerics.Ref.Comp

open ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.PB Topology Filter

theorem analytic_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {S T : Set X}
    (hS : A.IsAnalyticSubset S) (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∪ T) := by
  intro x
  obtain ⟨W, hW, hx, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hx', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hx, hx'⟩, r * r', fun i y => f (finProdFinEquiv.symm i).1 y *
    f' (finProdFinEquiv.symm i).2 y, fun i j t ht => ?_, ?_⟩
  · exact (hf _ j t ⟨ht.1, ht.2.1⟩).mul (hf' _ j t ⟨ht.1, ht.2.2⟩)
  · ext y
    have h1 := Set.ext_iff.1 hSW y
    have h2 := Set.ext_iff.1 hTW y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union] at h1 h2 ⊢
    constructor
    · rintro ⟨h | h, hy⟩
      · exact ⟨hy, fun i => by rw [(h1.1 ⟨h, hy.1⟩).2, zero_mul]⟩
      · exact ⟨hy, fun i => by rw [(h2.1 ⟨h, hy.2⟩).2, mul_zero]⟩
    · rintro ⟨hy, h⟩
      refine ⟨?_, hy⟩
      by_contra hn
      push Not at hn
      have a1 : ∃ i, f i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.1 (h1.2 ⟨hy.1, h3⟩).1
      have a2 : ∃ i, f' i y ≠ 0 := by
        by_contra h3
        push Not at h3
        exact hn.2 (h2.2 ⟨hy.2, h3⟩).1
      obtain ⟨i, hi⟩ := a1
      obtain ⟨i', hi'⟩ := a2
      have := h (finProdFinEquiv (i, i'))
      simp only [Equiv.symm_apply_apply] at this
      exact mul_ne_zero hi hi' this

theorem interior_union_empty {X : Type} [TopologicalSpace X] {S T : Set X} (hS : IsClosed S) (h1 : interior S = ∅)
    (h2 : interior T = ∅) : interior (S ∪ T) = ∅ := by
  rw [interior_union_isClosed_of_interior_empty hS h2, h1]

theorem interior_preimage {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [CompactSpace Z]
    {h : Z → Y} (hh : Continuous h) {N T : Set Y} (hN : IsClosed N) (hNi : interior (h ⁻¹' N) = ∅)
    (hfib : ∀ x ∉ N, (h ⁻¹' {x}).ncard = 1) (hT : interior T = ∅) : interior (h ⁻¹' T) = ∅ := by
  by_contra hne
  have hd : Dense (h ⁻¹' N)ᶜ := interior_eq_empty_iff_dense_compl.1 hNi
  obtain ⟨z, hzN, hzO⟩ := hd.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
  have hC : IsClosed (h '' (interior (h ⁻¹' T))ᶜ) :=
    (isOpen_interior.isClosed_compl.isCompact.image hh).isClosed
  have hO : IsOpen ((h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ) := hC.isOpen_compl.inter hN.isOpen_compl
  have hsub : (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ ⊆ T := by
    rintro x ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib x h2)
    have hcx : h c = x := by
      have : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
      exact this
    have : c ∈ interior (h ⁻¹' T) := by
      by_contra hn
      exact h1 ⟨c, hn, hcx⟩
    have h3 : c ∈ h ⁻¹' T := interior_subset this
    rw [← hcx]
    exact h3
  have hmem : h z ∈ (h '' (interior (h ⁻¹' T))ᶜ)ᶜ ∩ Nᶜ := by
    refine ⟨?_, hzN⟩
    rintro ⟨w, hw, hwz⟩
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hfib (h z) hzN)
    have e1 : w ∈ h ⁻¹' {h z} := hwz
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact hw ((e1.trans e2.symm) ▸ hzO)
  have := interior_maximal hsub hO hmem
  rw [hT] at this
  exact this

theorem degree_comp {e d : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] [CompactSpace Z] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {C : FinHolAtlas e Z}
    {π : Y → X} {h : Z → Y} {br S : Set X} {N : Set Y} (hπ : HoloMap B A π) (hh : HoloMap C B h) (hd : 0 < d)
    (hdπ : IsDegreeOff A B π d br) (hdh : IsDegreeOff B C h 1 N) (hS : A.IsAnalyticSubset S)
    (hSi : interior (π ⁻¹' S) = ∅) (hNS : N ⊆ π ⁻¹' S) : IsDegreeOff A C (π ∘ h) d (br ∪ S) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hdπ
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hdh
  have hcomp := CovMap.holoMap_comp hh hπ
  have hbrc : IsClosed br := isClosed_of_isAnalyticSubset A a1
  have hSi' : interior S = ∅ := by
    by_contra hne
    have hdn : Dense brᶜ := interior_eq_empty_iff_dense_compl.1 a2
    obtain ⟨x, hx, hxO⟩ := hdn.exists_mem_open isOpen_interior (Set.nonempty_iff_ne_empty.2 hne)
    have hpos : 0 < (π ⁻¹' {x}).ncard := by rw [a5 x hx]; exact hd
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
    have hy' : π y = x := hy
    have : y ∈ interior (π ⁻¹' S) := preimage_interior_subset_interior_preimage hπ.1 (by
      show π y ∈ interior S
      rw [hy']; exact hxO)
    rw [hSi] at this
    exact this
  have hU := analytic_union a1 hS
  refine ⟨hU, interior_union_empty hbrc a2 hSi', CovMap.Deg.isAnalyticSubset_preimage hcomp hU, ?_, ?_, ?_⟩
  · rw [Set.preimage_comp]
    refine interior_preimage hh.1 (isClosed_of_isAnalyticSubset B b1) b4 b5 ?_
    rw [Set.preimage_union]
    exact interior_union_empty (hbrc.preimage hπ.1) a4 hSi
  · intro x hx
    have hx1 : x ∉ br := fun h => hx (Or.inl h)
    have hx2 : x ∉ S := fun h => hx (Or.inr h)
    have hN : ∀ y, π y = x → y ∉ N := fun y hy hn => hx2 (hy ▸ hNS hn)
    rw [← a5 x hx1]
    have himg : h '' ((π ∘ h) ⁻¹' {x}) = π ⁻¹' {x} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 y (hN y hy))
        have hcx : h c = y := by
          have : c ∈ h ⁻¹' {y} := by rw [hc]; rfl
          exact this
        refine ⟨c, ?_, hcx⟩
        show π (h c) = x
        rw [hcx]; exact hy
    rw [← himg]
    refine (Set.ncard_image_of_injOn ?_).symm
    intro z hz w _ hzw
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (b5 (h z) (hN _ hz))
    have e1 : w ∈ h ⁻¹' {h z} := hzw.symm
    have e2 : z ∈ h ⁻¹' {h z} := rfl
    rw [hc] at e1 e2
    exact e2.trans e1.symm
  · intro j k y hy hnot hk
    have hnot1 : (C.chart j).symm y ∉ h ⁻¹' N := fun hn => hnot (Or.inr (hNS hn))
    have hnot2 : h ((C.chart j).symm y) ∉ π ⁻¹' br := fun hn => hnot (Or.inl hn)
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp' : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp']
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact a6 l k _ hQt (by rw [hu]; exact hnot2) hk'
    · rw [hQdef]
      exact b6 j l y hy hnot1 hl

end RootFieldNumerics.Ref.Comp
