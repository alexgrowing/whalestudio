import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

namespace GlobalTheory.SBOrth

open Set Function

variable {Z : Type} [TopologicalSpace Z]

theorem indicator_mem {V : Set Z} (hV : IsClopen V) {f : Z → ℂ} (hf : f ∈ SB Z) :
    V.indicator f ∈ SB Z := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, h2.mono (by rw [Set.support_indicator]; exact inter_subset_right)⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ V
  · filter_upwards [hV.isOpen.mem_nhds hx, ((IsLocallyConstant.iff_eventually_eq f).1 h1 x)] with y hy hy'
    simp [Set.indicator_apply, hy, hx, hy']
  · filter_upwards [hV.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ V := hy
    simp [Set.indicator_apply, hy', hx]

def PairNull (β : (Z → ℂ) → (Z → ℂ) → ℂ) (U V : Set Z) : Prop :=
  ∀ f' ∈ SB Z, ∀ g' ∈ SB Z, (∀ z ∉ U, f' z = 0) → (∀ z ∉ V, g' z = 0) → β f' g' = 0

theorem PairNull.mono {β : (Z → ℂ) → (Z → ℂ) → ℂ} {U V U' V' : Set Z} (h : PairNull β U V)
    (hU : U' ⊆ U) (hV : V' ⊆ V) : PairNull β U' V' := by
  intro f' hf' g' hg' h1 h2
  exact h f' hf' g' hg' (fun z hz => h1 z (fun h => hz (hU h))) (fun z hz => h2 z (fun h => hz (hV h)))

theorem PairNull.union_right {β : (Z → ℂ) → (Z → ℂ) → ℂ}
    (hadd2 : ∀ f ∈ SB Z, ∀ g ∈ SB Z, ∀ g' ∈ SB Z, β f (g + g') = β f g + β f g')
    {U V V' : Set Z} (hVc : IsClopen V) (h : PairNull β U V) (h' : PairNull β U V') :
    PairNull β U (V ∪ V') := by
  intro f' hf' g' hg' hU hVV'
  rw [← Set.indicator_self_add_compl V g',
    hadd2 f' hf' _ (indicator_mem hVc hg') _ (indicator_mem hVc.compl hg')]
  have a := h f' hf' (V.indicator g') (indicator_mem hVc hg') hU
    (fun z hz => by simp [Set.indicator_apply, hz])
  have b := h' f' hf' (Vᶜ.indicator g') (indicator_mem hVc.compl hg') hU
    (fun z hz => by
      by_cases hzV : z ∈ V
      · simp [Set.indicator_apply, hzV]
      · have : g' z = 0 := hVV' z (by simp [hzV, hz])
        simp [Set.indicator_apply, hzV, this])
  rw [a, b, add_zero]

theorem base (β : (Z → ℂ) → (Z → ℂ) → ℂ)
    (hsm : ∀ (a : ℂ), ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (a • f) g = a * β f g ∧ β f (a • g) = starRingEnd ℂ a * β f g)
    (x y : Z) (χ : Z → ℂ) (hχlc : IsLocallyConstant χ) (hχn : ∀ z, ‖χ z‖ = 1) (hχne : χ x ≠ χ y)
    (hχβ : ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (χ * f) (χ * g) = β f g) :
    PairNull β (χ ⁻¹' {χ x}) (χ ⁻¹' {χ y}) := by
  intro f' hf' g' hg' hU hV
  have e1 : χ * f' = χ x • f' := by
    funext z
    by_cases hz : χ z = χ x
    · simp [hz]
    · simp [hU z hz]
  have e2 : χ * g' = χ y • g' := by
    funext z
    by_cases hz : χ z = χ y
    · simp [hz]
    · simp [hV z hz]
  have key := hχβ f' hf' g' hg'
  rw [e1, e2, (hsm _ f' hf' _ (Submodule.smul_mem _ _ hg')).1, (hsm _ f' hf' g' hg').2] at key
  have hy : starRingEnd ℂ (χ y) * χ y = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn y]; simp
  have hne : χ x * starRingEnd ℂ (χ y) ≠ 1 := by
    intro h
    apply hχne
    calc χ x = χ x * (starRingEnd ℂ (χ y) * χ y) := by rw [hy, mul_one]
      _ = (χ x * starRingEnd ℂ (χ y)) * χ y := by ring
      _ = χ y := by rw [h, one_mul]
  have h0 : (1 - χ x * starRingEnd ℂ (χ y)) * β f' g' = 0 := by
    linear_combination (-1 : ℂ) * key
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

theorem support_isCompact {f : Z → ℂ} (hf : f ∈ SB Z) : IsCompact (support f) := by
  have hcl : IsClosed (support f) := by
    have : support f = (f ⁻¹' {0})ᶜ := by ext z; simp
    rw [this]
    exact (hf.1.isOpen_fiber 0).isClosed_compl
  exact hf.2.isCompact.of_isClosed_subset hcl (subset_tsupport f)

end GlobalTheory.SBOrth

open Set Function

theorem GlobalTheory.SBOrth.sesq_eq_zero_of_mul_eq_zero : ∀ (Z : Type) [TopologicalSpace Z] (β : (Z → ℂ) → (Z → ℂ) → ℂ),
    (∀ f ∈ SB Z, ∀ f' ∈ SB Z, ∀ g ∈ SB Z, β (f + f') g = β f g + β f' g) → (∀ f ∈ SB Z, ∀ g ∈ SB Z, ∀ g' ∈ SB Z, β f (g + g') = β f g + β f g') →
    (∀ (a : ℂ), ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (a • f) g = a * β f g ∧ β f (a • g) = starRingEnd ℂ a * β f g) →
    (∀ x y : Z, x ≠ y → ∃ χ : Z → ℂ, IsLocallyConstant χ ∧ (∀ z, ‖χ z‖ = 1) ∧ χ x ≠ χ y ∧ ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (χ * f) (χ * g) = β f g) →
    ∀ f ∈ SB Z, ∀ g ∈ SB Z, (∀ x, f x * g x = 0) → β f g = 0 := by
  intro Z _ β hadd1 hadd2 hsm hsep f hf g hg hfg
  have hz1 : ∀ f' ∈ SB Z, ∀ g' ∈ SB Z, (∀ z, f' z = 0) → β f' g' = 0 := by
    intro f' hf' g' hg' h0
    have : f' = (0:ℂ) • f' := by funext z; simp [h0 z]
    rw [this, (hsm 0 f' hf' g' hg').1, zero_mul]
  have hz2 : ∀ f' ∈ SB Z, ∀ g' ∈ SB Z, (∀ z, g' z = 0) → β f' g' = 0 := by
    intro f' hf' g' hg' h0
    have : g' = (0:ℂ) • g' := by funext z; simp [h0 z]
    rw [this, (hsm 0 f' hf' g' hg').2, map_zero, zero_mul]

  have inner : ∀ x, f x ≠ 0 → ∃ U V : Set Z, IsClopen U ∧ IsClopen V ∧ x ∈ U ∧
      support g ⊆ V ∧ GlobalTheory.SBOrth.PairNull β U V := by
    intro x hx
    refine (GlobalTheory.SBOrth.support_isCompact hg).induction_on
      (p := fun S => ∃ U V : Set Z, IsClopen U ∧ IsClopen V ∧ x ∈ U ∧ S ⊆ V ∧
        GlobalTheory.SBOrth.PairNull β U V) ?_ ?_ ?_ ?_
    · refine ⟨univ, ∅, isClopen_univ, isClopen_empty, mem_univ _, subset_rfl, ?_⟩
      intro f' hf' g' hg' _ h2
      exact hz2 f' hf' g' hg' (fun z => h2 z (by simp))
    · rintro S T hST ⟨U, V, hU, hV, hxU, hTV, hP⟩
      exact ⟨U, V, hU, hV, hxU, hST.trans hTV, hP⟩
    · rintro S T ⟨U, V, hU, hV, hxU, hSV, hP⟩ ⟨U', V', hU', hV', hxU', hTV', hP'⟩
      refine ⟨U ∩ U', V ∪ V', hU.inter hU', hV.union hV', ⟨hxU, hxU'⟩,
        union_subset_union hSV hTV', ?_⟩
      exact GlobalTheory.SBOrth.PairNull.union_right hadd2 hV
        (hP.mono inter_subset_left subset_rfl) (hP'.mono inter_subset_right subset_rfl)
    · intro y hy
      have hxy : x ≠ y := by
        rintro rfl
        exact hy ((mul_eq_zero.1 (hfg x)).resolve_left hx)
      obtain ⟨χ, hχlc, hχn, hχne, hχβ⟩ := hsep x y hxy
      refine ⟨χ ⁻¹' {χ y}, mem_nhdsWithin_of_mem_nhds ((hχlc.isOpen_fiber _).mem_nhds rfl), ?_⟩
      exact ⟨χ ⁻¹' {χ x}, χ ⁻¹' {χ y}, hχlc.isClopen_fiber _, hχlc.isClopen_fiber _, rfl,
        subset_rfl, GlobalTheory.SBOrth.base β hsm x y χ hχlc hχn hχne hχβ⟩

  obtain ⟨U, hUc, hfU, hQ⟩ : ∃ U : Set Z, IsClopen U ∧ support f ⊆ U ∧
      ∀ f' ∈ SB Z, (∀ z ∉ U, f' z = 0) → β f' g = 0 := by
    refine (GlobalTheory.SBOrth.support_isCompact hf).induction_on
      (p := fun S => ∃ U : Set Z, IsClopen U ∧ S ⊆ U ∧
        ∀ f' ∈ SB Z, (∀ z ∉ U, f' z = 0) → β f' g = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, ?_⟩
      intro f' hf' h1
      exact hz1 f' hf' g hg (fun z => h1 z (by simp))
    · rintro S T hST ⟨U, hU, hTU, hQ⟩
      exact ⟨U, hU, hST.trans hTU, hQ⟩
    · rintro S T ⟨U, hU, hSU, hQ⟩ ⟨U', hU', hTU', hQ'⟩
      refine ⟨U ∪ U', hU.union hU', union_subset_union hSU hTU', ?_⟩
      intro f' hf' h1
      rw [← Set.indicator_self_add_compl U f',
        hadd1 _ (GlobalTheory.SBOrth.indicator_mem hU hf') _ (GlobalTheory.SBOrth.indicator_mem hU.compl hf') g hg]
      have a := hQ (U.indicator f') (GlobalTheory.SBOrth.indicator_mem hU hf')
        (fun z hz => by simp [Set.indicator_apply, hz])
      have b := hQ' (Uᶜ.indicator f') (GlobalTheory.SBOrth.indicator_mem hU.compl hf')
        (fun z hz => by
          by_cases hzU : z ∈ U
          · simp [Set.indicator_apply, hzU]
          · have : f' z = 0 := h1 z (by simp [hzU, hz])
            simp [Set.indicator_apply, hzU, this])
      rw [a, b, add_zero]
    · intro x hx
      obtain ⟨U, V, hU, hV, hxU, hgV, hP⟩ := inner x hx
      refine ⟨U, mem_nhdsWithin_of_mem_nhds (hU.isOpen.mem_nhds hxU), U, hU, subset_rfl, ?_⟩
      intro f' hf' h1
      exact hP f' hf' g hg h1 (fun z hz => by
        by_contra hne
        exact hz (hgV hne))
  exact hQ f hf (fun z hz => by
    by_contra hne
    exact hz (hfU hne))
