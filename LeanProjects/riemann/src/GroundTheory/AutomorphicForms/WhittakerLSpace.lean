import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.LocallyConstantCompact

namespace GroundTheory.Automorphic

namespace Whittaker

open Set Topology

variable {X : Type*} [TopologicalSpace X]

def supportedIn (U : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U}
  add_mem' {f g} hf hg := ⟨(locallyConstantCompactSupport X ℂ ℂ).add_mem hf.1 hg.1,
    (Function.support_add f g).trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨(locallyConstantCompactSupport X ℂ ℂ).zero_mem, by simp⟩
  smul_mem' c f hf := ⟨(locallyConstantCompactSupport X ℂ ℂ).smul_mem c hf.1,
    (Function.support_const_smul_subset c f).trans hf.2⟩

theorem mem_supportedIn {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U :=
  Iff.rfl

theorem supportedIn_mono {U V : Set X} (h : U ⊆ V) : supportedIn U ≤ supportedIn V :=
  fun _ hf => ⟨hf.1, hf.2.trans h⟩

def vanishingOn (Z : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ x ∈ Z, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

omit [TopologicalSpace X] in
theorem mem_vanishingOn {Z : Set X} {f : X → ℂ} : f ∈ vanishingOn Z ↔ ∀ x ∈ Z, f x = 0 :=
  Iff.rfl

omit [TopologicalSpace X] in
theorem vanishingOn_anti {Z Z' : Set X} (h : Z ⊆ Z') : vanishingOn Z' ≤ vanishingOn Z :=
  fun _ hf x hx => hf x (h hx)

theorem isClosed_support_of_isLocallyConstant {f : X → ℂ} (hf : IsLocallyConstant f) :
    IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by
    ext x
    simp [Function.mem_support]
  rw [this]
  exact (hf.isOpen_fiber 0).isClosed_compl

theorem isCompact_support {f : X → ℂ} (hf : f ∈ locallyConstantCompactSupport X ℂ ℂ) :
    IsCompact (Function.support f) :=
  hf.2.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf.1) (subset_tsupport f)

theorem indicator_mul_mem {U A : Set X} (hA : IsClopen A) {f : X → ℂ}
    (hf : f ∈ supportedIn U) : (fun x => A.indicator 1 x * f x) ∈ supportedIn U := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : IsLocallyConstant (A.indicator (1 : X → ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const X (1 : ℂ)) hA).isLocallyConstant
    exact h1.comp₂ hf.1.1 (· * ·)
  · refine hf.1.2.mono fun x hx => ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])
  · intro x hx
    refine hf.2 ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])

omit [TopologicalSpace X] in
theorem support_indicator_mul_subset {A : Set X} {f : X → ℂ} :
    Function.support (fun x => A.indicator 1 x * f x) ⊆ A ∩ Function.support f := by
  intro x hx
  refine ⟨?_, fun h => hx (by simp [h])⟩
  by_contra h
  exact hx (by simp [Set.indicator_of_notMem h])

section LSpace

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem exists_isCompact_isOpen_between {A V : Set X} (hA : IsCompact A) (hV : IsOpen V)
    (hAV : A ⊆ V) : ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ A ⊆ B ∧ B ⊆ V := by
  have h : ∀ x ∈ A, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ x ∈ B ∧ B ⊆ V := fun x hx =>
    exists_isCompact_isOpen_subset (hV.mem_nhds (hAV hx))
  choose B hBc hBo hxB hBV using h
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : A => B x x.2) (fun x => hBo x x.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩)
  refine ⟨⋃ x ∈ s, B x x.2, s.isCompact_biUnion fun x _ => hBc x x.2,
    isOpen_biUnion fun x _ => hBo x x.2, hs, iUnion₂_subset fun x _ => hBV x x.2⟩

theorem exists_isCompact_isOpen_inter_eq {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U)
    (hAO : A ⊆ O) (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧ B ∩ O = A := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hAo
  have hAV : A ⊆ V := fun x hx => by
    have : (⟨x, hAO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := by rw [hV]; exact hx
    exact this
  obtain ⟨B, hBc, hBo, hAB, hBV⟩ :=
    exists_isCompact_isOpen_between hAc (hVo.inter hU) (subset_inter hAV (hAO.trans hOU))
  refine ⟨B, hBc, hBo, hBV.trans inter_subset_right, subset_antisymm ?_ ?_⟩
  · rintro x ⟨hxB, hxO⟩
    have : (⟨x, hxO⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := (hBV hxB).1
    rw [hV] at this
    exact this
  · exact fun x hx => ⟨hAB hx, hAO hx⟩

theorem exists_lift {U O : Set X} (hU : IsOpen U) (hOU : O ⊆ U) {φ : O → ℂ}
    (hφ : φ ∈ locallyConstantCompactSupport O ℂ ℂ) :
    ∃ f ∈ supportedIn U, ∀ x : O, f x = φ x := by
  classical
  have key : ∀ c : ℂ, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧
      (c ≠ 0 → ∀ x : O, (x : X) ∈ B ↔ φ x = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isOpen_empty, empty_subset _, fun h => absurd hc h⟩
    obtain ⟨hFc, hFo⟩ := isCompact_isOpen_fiber hφ hc
    have hAc : IsCompact ((Subtype.val : O → X) '' {x | φ x = c}) :=
      hFc.image continuous_subtype_val
    have hAo : IsOpen ((Subtype.val : O → X) ⁻¹' ((Subtype.val : O → X) '' {x | φ x = c})) := by
      rwa [preimage_image_eq _ Subtype.val_injective]
    obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU
      (by rintro _ ⟨x, -, rfl⟩; exact x.2) hAc hAo
    refine ⟨B, hBc, hBo, hBU, fun _ x => ?_⟩
    constructor
    · intro hx
      have : (x : X) ∈ B ∩ O := ⟨hx, x.2⟩
      rw [hBO] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [← Subtype.ext hyx]
      exact hy
    · intro hx
      have : (x : X) ∈ (Subtype.val : O → X) '' {x | φ x = c} := ⟨x, hx, rfl⟩
      rw [← hBO] at this
      exact this.1
  choose B hBc hBo hBU hBO using key
  have hfin := range_finite_of_mem_locallyConstantCompactSupport hφ
  refine ⟨∑ c ∈ hfin.toFinset.filter (· ≠ 0), (B c).indicator (fun _ => c), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c _ => ⟨?_, ?_⟩
    · exact indicator_mem_locallyConstantCompactSupport (hBc c) (hBo c) c
    · exact (Set.support_indicator_subset).trans (hBU c)
  · intro x
    rw [Finset.sum_apply]
    by_cases hx : φ x = 0
    · rw [hx]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      refine Set.indicator_of_notMem (fun h => hc0 ?_) _
      rw [← hx]
      exact ((hBO c hc0 x).1 h).symm
    · rw [Finset.sum_eq_single (φ x)]
      · exact Set.indicator_of_mem ((hBO _ hx x).2 rfl) _
      · intro c hc hcx
        exact Set.indicator_of_notMem
          (fun h => hcx ((hBO c (Finset.mem_filter.1 hc).2 x).1 h).symm) _
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (mem_range_self x), hx⟩) h

theorem exists_lift_indicator {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U) (hAO : A ⊆ O)
    (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ f ∈ supportedIn U, ∀ x ∈ O, f x = A.indicator 1 x := by
  obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU hAO hAc hAo
  refine ⟨B.indicator 1, ⟨indicator_mem_locallyConstantCompactSupport hBc hBo 1,
    Set.support_indicator_subset.trans hBU⟩, fun x hx => ?_⟩
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := by
      have : x ∈ B ∩ O := by rw [hBO]; exact hxA
      exact this.1
    rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxB]
  · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem]
    intro hxB
    exact hxA (hBO ▸ (⟨hxB, hx⟩ : x ∈ B ∩ O))

theorem exists_isClopen_mem_disjoint {Q : Set X} (hQ : IsCompact Q) {y : X} (hy : y ∉ Q) :
    ∃ V : Set X, IsClopen V ∧ y ∈ V ∧ Disjoint V Q := by
  obtain ⟨V, hVc, hVo, hyV, hVQ⟩ :=
    exists_isCompact_isOpen_subset (hQ.isClosed.isOpen_compl.mem_nhds hy)
  exact ⟨V, ⟨hVc.isClosed, hVo⟩, hyV, Set.subset_compl_iff_disjoint_right.mp hVQ⟩

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in

theorem mem_of_forall_fiber {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {U C : Set X} (hC : IsClosed C) {p : X → Y}
    (hp : Continuous p) {W : Submodule ℂ (X → ℂ)}
    (hWK : supportedIn U ⊓ vanishingOn C ≤ W)
    (hWmul : ∀ V : Set Y, IsClopen V → ∀ w ∈ W, (fun x => (p ⁻¹' V).indicator 1 x * w x) ∈ W)
    {g : X → ℂ} (hg : g ∈ supportedIn U)
    (hfib : ∀ y, g ∈ W ⊔ (supportedIn U ⊓ vanishingOn (C ∩ p ⁻¹' {y}))) : g ∈ W := by
  classical

  let good : Set Y → Prop := fun V => (fun x => (p ⁻¹' V).indicator 1 x * g x) ∈ W
  have hloc : ∀ y, ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ good V := by
    intro y
    obtain ⟨c, hcW, k, hk, hck⟩ := Submodule.mem_sup.1 (hfib y)
    have hQ : IsCompact (p '' (C ∩ Function.support k)) :=
      ((isCompact_support hk.1.1).inter_left hC).image hp
    have hyQ : y ∉ p '' (C ∩ Function.support k) := by
      rintro ⟨x, ⟨hxC, hxk⟩, hxy⟩
      exact hxk (hk.2 x ⟨hxC, hxy⟩)
    obtain ⟨V, hV, hyV, hVQ⟩ := exists_isClopen_mem_disjoint hQ hyQ
    refine ⟨V, hV, hyV, ?_⟩
    have hsplit : (fun x => (p ⁻¹' V).indicator 1 x * g x) =
        (fun x => (p ⁻¹' V).indicator 1 x * c x) + (fun x => (p ⁻¹' V).indicator 1 x * k x) := by
      funext x
      simp only [Pi.add_apply, ← mul_add, ← hck]
    show _ ∈ W
    rw [hsplit]
    refine W.add_mem (hWmul V hV c hcW) (hWK ⟨indicator_mul_mem (hV.preimage hp) hk.1, ?_⟩)
    intro x hxC
    by_cases hxV : x ∈ p ⁻¹' V
    · have : k x = 0 := by
        by_contra hkx
        exact Set.disjoint_left.1 hVQ hxV ⟨x, ⟨hxC, hkx⟩, rfl⟩
      simp [this]
    · simp [Set.indicator_of_notMem hxV]
  choose V hVc hyV hVg using hloc

  have hQ : IsCompact (p '' (C ∩ Function.support g)) :=
    ((isCompact_support hg.1).inter_left hC).image hp
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover V (fun y => (hVc y).isOpen)
    (fun y _ => mem_iUnion.2 ⟨y, hyV y⟩)

  have hunion : ∀ t : Finset Y, IsClopen (⋃ y ∈ t, V y) ∧ good (⋃ y ∈ t, V y) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨by simp [isClopen_empty], ?_⟩
      show _ ∈ W
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, preimage_empty,
        Set.indicator_empty, zero_mul]
      exact W.zero_mem
    | insert a t hat ih =>
      obtain ⟨ht, hgt⟩ := ih
      have hcl : IsClopen (V a ∪ ⋃ y ∈ t, V y) := (hVc a).union ht
      refine ⟨by simpa [Finset.set_biUnion_insert] using hcl, ?_⟩
      show _ ∈ W
      have hmul := hWmul (V a) (hVc a) _ hgt
      have e : (fun x => (p ⁻¹' ⋃ y ∈ insert a t, V y).indicator 1 x * g x) =
          (fun x => (p ⁻¹' V a).indicator 1 x * g x) +
            (fun x => (p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x) -
            (fun x => (p ⁻¹' V a).indicator 1 x *
              ((p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x)) := by
        funext x
        simp only [Finset.set_biUnion_insert, Pi.add_apply, Pi.sub_apply, preimage_union]
        by_cases h1 : x ∈ p ⁻¹' V a <;> by_cases h2 : x ∈ p ⁻¹' ⋃ y ∈ t, V y <;>
          simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
      rw [e]
      exact W.sub_mem (W.add_mem (hVg a) hgt) hmul
  obtain ⟨-, hgood⟩ := hunion s
  have hrest : (g - fun x => (p ⁻¹' ⋃ y ∈ s, V y).indicator 1 x * g x) ∈ W := by
    refine hWK ⟨(supportedIn U).sub_mem hg
      (indicator_mul_mem ((hunion s).1.preimage hp) hg), ?_⟩
    intro x hxC
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hx : x ∈ p ⁻¹' ⋃ y ∈ s, V y := hs ⟨x, ⟨hxC, hgx⟩, rfl⟩
      simp only [Pi.sub_apply]
      rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul, sub_self]
  have := W.add_mem hrest hgood
  simpa using this

theorem supportedIn_le_of_local {V : Set X} {M : Submodule ℂ (X → ℂ)}
    (hloc : ∀ x ∈ V, ∃ V' : Set X, IsOpen V' ∧ x ∈ V' ∧ supportedIn V' ≤ M) :
    supportedIn V ≤ M := by
  classical
  intro f hf
  have hB : ∀ x ∈ V, ∃ B : Set X, IsClopen B ∧ x ∈ B ∧ supportedIn B ≤ M := by
    intro x hx
    obtain ⟨V', hV'o, hxV', hV'M⟩ := hloc x hx
    obtain ⟨B, hBc, hBo, hxB, hBV'⟩ := exists_isCompact_isOpen_subset (hV'o.mem_nhds hxV')
    exact ⟨B, ⟨hBc.isClosed, hBo⟩, hxB, (supportedIn_mono hBV').trans hV'M⟩
  choose! B hBc hxB hBM using hB
  obtain ⟨s, hsV, hsfin, hs⟩ := (isCompact_support hf.1).elim_finite_subcover_image
    (b := V) (c := B) (fun x hx => (hBc x hx).isOpen)
    (fun x hx => mem_iUnion₂.2 ⟨x, hf.2 hx, hxB x (hf.2 hx)⟩)
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ V → ∀ g ∈ supportedIn V,
      Function.support g ⊆ ⋃ x ∈ t, B x → g ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ g _ hg
      have : g = 0 := by
        funext x
        by_contra h
        simpa using hg h
      rw [this]
      exact M.zero_mem
    | insert a t hat ih =>
      intro htV g hg hgs
      have haV : a ∈ V := htV (by simp)
      have e : g = (fun x => (B a).indicator 1 x * g x) +
          (fun x => (B a)ᶜ.indicator 1 x * g x) := by
        funext x
        by_cases h : x ∈ B a <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      rw [e]
      refine M.add_mem (hBM a haV ⟨(indicator_mul_mem (hBc a haV) hg).1, ?_⟩)
        (ih (fun x hx => htV (by simp [hx])) _ (indicator_mul_mem (hBc a haV).compl hg) ?_)
      · exact support_indicator_mul_subset.trans inter_subset_left
      · intro x hx
        obtain ⟨hxB, hxg⟩ := support_indicator_mul_subset hx
        have := hgs hxg
        rw [Finset.set_biUnion_insert] at this
        rcases this with h | h
        · exact absurd h hxB
        · simpa using h
  exact key hsfin.toFinset (fun x hx => hsV (by simpa using hx)) f hf (by simpa using hs)

end LSpace

end Whittaker

end GroundTheory.Automorphic
