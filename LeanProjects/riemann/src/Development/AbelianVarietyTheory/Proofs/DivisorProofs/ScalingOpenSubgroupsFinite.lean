import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BoxCosetSum

variable {F : Type} [Field F] [NumberField F]

theorem continuous_evalV' (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

theorem eventually_evalV_mem_integers (x : FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ v.adicCompletionIntegers F := x.2

theorem isOpen_box (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
  have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 hBf
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have e : {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} =
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} ∩
        ⋂ v ∈ hT.toFinset, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) ⁻¹' (B v : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.Finite.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun v => hBO v (h v), fun v _ => h v⟩
    · rintro ⟨h1, h2⟩ v
      by_cases hv : (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F
      · have : x v ∈ (B v : Set (v.adicCompletion F)) := by rw [hv]; exact h1 v
        exact this
      · exact h2 v hv
  rw [e]
  exact hO.inter (isOpen_biInter_finset fun v _ => (hBo v).preimage (continuous_evalV' v))

def boxSub (κ : Type) (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {u | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v}
  add_mem' := by
    intro a b ha hb i v
    simp only [Pi.add_apply, map_add]
    exact (B v).add_mem (ha i v) (hb i v)
  zero_mem' := by
    intro i v
    simp only [Pi.zero_apply, map_zero]
    exact (B v).zero_mem
  neg_mem' := by
    intro a ha i v
    simp only [Pi.neg_apply, map_neg]
    exact (B v).neg_mem (ha i v)

theorem mem_boxSub {κ : Type} {B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)}
    {u : κ → FiniteAdeleRing (𝓞 F) F} :
    u ∈ boxSub κ B ↔ ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v := Iff.rfl

theorem isOpen_boxSub (κ : Type) [Finite κ] (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBo : ∀ v, IsOpen (B v : Set (v.adicCompletion F)))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) :
    IsOpen (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have e : (boxSub κ B : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun u : κ → FiniteAdeleRing (𝓞 F) F => u i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x ∈ B v} := by
    ext u
    simp only [SetLike.mem_coe, mem_boxSub, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_box B hBo hBO hBf).preimage (continuous_apply i)

theorem finprod_indicator_eq (κ : Type) [Finite κ]
    (B : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F))
    (hBO : ∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F)
    (hBf : ∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F)
    (r y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))) =
      Set.indicator {z | z - r ∈ boxSub κ B} (fun _ => (1 : ℂ)) y := by
  have key : ∀ v, ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}) ↔
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ B v := by
    intro v
    simp only [Set.mem_setOf_eq, Pi.sub_apply, map_sub]
  by_cases h : y - r ∈ boxSub κ B
  · rw [Set.indicator_of_mem (show y ∈ {z | z - r ∈ boxSub κ B} from h)]
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [Set.indicator_of_mem ((key v).2 fun i => h i v), Pi.one_apply]
  · rw [Set.indicator_of_notMem (show y ∉ {z | z - r ∈ boxSub κ B} from h)]
    rw [mem_boxSub] at h
    push_neg at h
    obtain ⟨i0, v0, hv0⟩ := h
    apply finprod_eq_zero _ v0
    · rw [Set.indicator_of_notMem]
      rw [key v0]
      exact fun H => hv0 (H i0)
    · have hT : {v | ¬ (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F}.Finite :=
        Filter.eventually_cofinite.1 hBf
      have hI : (⋃ i, {v | ¬ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈ v.adicCompletionIntegers F}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (eventually_evalV_mem_integers ((y - r) i))
      refine (hT.union hI).subset ?_
      intro v hv
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
      apply hv
      dsimp only
      rw [Set.indicator_of_mem, Pi.one_apply]
      rw [key v]
      intro i
      have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v ((y - r) i) ∈
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := hc.2 i
      rw [← hc.1] at h2
      exact h2

theorem eq_sum_finprod_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y) →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F), g = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        ∏ᶠ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
          (1 : (κ → v.adicCompletion F) → ℂ) (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ B hBo hBO hBf g hg hinv
  classical
  set U := boxSub κ B with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_boxSub κ B hBo hBO hBf
  have hK : IsCompact (tsupport g) := hg
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, finprod_indicator_eq κ B hBO hBf]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · rw [Set.indicator_of_mem (show x ∈ {z | z - r0 ∈ boxSub κ B} from hxr0), mul_one]
      have := hinv r0 (x - r0) hxr0
      rwa [add_sub_cancel] at this
    · intro r hr hne
      have hm : x ∉ {z | z - r ∈ boxSub κ B} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {z | z - r ∈ boxSub κ B} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.BoxCosetSum

end
