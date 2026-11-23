import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

noncomputable section
namespace GlobalTheory.KSp.FourInv

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

theorem ne_zero (he : IsPair e) (x y : X) : e x y ≠ 0 := by
  intro h
  have h1 := he.norm x y
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem add_right (he : IsPair e) (x y y' : X) : e x (y + y') = e x y * e x y' := by
  rw [he.symm x (y + y'), he.add y y' x, he.symm y x, he.symm y' x]

theorem zero_right (he : IsPair e) (x : X) : e x 0 = 1 := by
  have h := add_right he x 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (ne_zero he x 0) (by rw [mul_one]; exact h.symm)

def ann (he : IsPair e) (L : Set X) : AddSubgroup X where
  carrier := {z | ∀ y ∈ L, e y z = 1}
  zero_mem' := fun y _ => zero_right he y
  add_mem' := fun {a b} ha hb y hy => by rw [add_right he, ha y hy, hb y hy, one_mul]
  neg_mem' := fun {a} ha y hy => by
    have h := add_right he y a (-a)
    rw [add_neg_cancel, zero_right he, ha y hy, one_mul] at h
    exact h.symm

theorem isOpen_ann [IsTopologicalAddGroup X] (he : IsPair e) {L : Set X} (hL : IsCompact L) :
    IsOpen (ann he L : Set X) := by
  have hS : IsOpen {p : X × X | e p.1 p.2 = 1} := he.lc.isOpen_fiber 1
  have hsub : L ×ˢ ({0} : Set X) ⊆ {p : X × X | e p.1 p.2 = 1} := by
    rintro ⟨y, z⟩ ⟨_, hz⟩
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact zero_right he y
  obtain ⟨u, v, -, hv, hLu, h0v, huv⟩ := generalized_tube_lemma hL isCompact_singleton hS hsub
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  refine Filter.mem_of_superset (hv.mem_nhds (h0v (Set.mem_singleton 0))) ?_
  intro z hz
  show ∀ y ∈ L, e y z = 1
  intro y hy
  exact huv (show (y, z) ∈ u ×ˢ v from ⟨hLu hy, hz⟩)

theorem exists_invariant [IsTopologicalAddGroup X] {f : X → ℂ} (hf : f ∈ SB X) :
    ∃ U ∈ 𝓝 (0 : X), ∀ M : AddSubgroup X, (M : Set X) ⊆ U → ∀ t ∈ M, ∀ x, f (x + t) = f x := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hS : IsOpen {p : X × X | f (p.1 + p.2) - f p.1 = 0} :=
    ((hf'.1.comp_continuous continuous_add).comp₂ (hf'.1.comp_continuous continuous_fst)
      (fun a b : ℂ => a - b)).isOpen_fiber 0
  have hsub : tsupport f ×ˢ ({0} : Set X) ⊆ {p : X × X | f (p.1 + p.2) - f p.1 = 0} := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    simp
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hf'.2.isCompact isCompact_singleton hS hsub
  refine ⟨v, hv.mem_nhds (h0v (Set.mem_singleton 0)), fun M hM t ht x => ?_⟩
  have key : ∀ y ∈ tsupport f, ∀ s ∈ M, f (y + s) = f y := fun y hy s hs => by
    have h := huv (show (y, s) ∈ u ×ˢ v from ⟨hKu hy, hM hs⟩)
    exact sub_eq_zero.mp h
  by_cases hx : x ∈ tsupport f
  · exact key x hx t ht
  · by_cases hxt : x + t ∈ tsupport f
    · have h := key (x + t) hxt (-t) (M.neg_mem ht)
      rw [add_neg_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxt]

theorem indicator_invariant (L : AddSubgroup X) (c : ℂ) :
    ∀ t ∈ L, ∀ x, (L : Set X).indicator (fun _ => c) (x + t) = (L : Set X).indicator (fun _ => c) x := by
  intro t ht x
  by_cases hx : x ∈ (L : Set X)
  · have hxt : x + t ∈ (L : Set X) := L.add_mem hx ht
    rw [Set.indicator_of_mem hxt, Set.indicator_of_mem hx]
  · have hxt : x + t ∉ (L : Set X) := fun h => hx (by simpa using L.sub_mem h ht)
    rw [Set.indicator_of_notMem hxt, Set.indicator_of_notMem hx]

theorem indicator_mem [IsTopologicalAddGroup X] [T2Space X] (L : AddSubgroup X) (hc : IsCompact (L : Set X))
    (ho : IsOpen (L : Set X)) : (L : Set X).indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  have hcl : IsClosed (L : Set X) := AddSubgroup.isClosed_of_isOpen L ho
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (L : Set X)
    · exact ⟨(L : Set X), ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨(L : Set X)ᶜ, hcl.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _

variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem four_eq_zero (he : IsPair e) {M : Set X} {f : X → ℂ}
    (hs : ∀ t ∈ M, ∀ x, f (x + t) = f x) {y : X} (hy : y ∉ ann he M) : four μ e f y = 0 := by
  have hy' : ¬ ∀ t ∈ M, e t y = 1 := hy
  simp only [not_forall] at hy'
  obtain ⟨t, ht, hne⟩ := hy'
  have hne' : e y t ≠ 1 := by rwa [he.symm]
  have key : four μ e f y = e y t * four μ e f y := by
    simp only [four]
    calc ∫ z, e y z * f z ∂μ = ∫ z, e y (t + z) * f (t + z) ∂μ :=
          (integral_add_left_eq_self (fun z => e y z * f z) t).symm
      _ = ∫ z, e y t * (e y z * f z) ∂μ := by
          congr 1; ext z
          rw [add_right he, add_comm t z, hs t ht z]; ring
      _ = e y t * ∫ z, e y z * f z ∂μ := integral_const_mul _ _
  by_contra h
  exact hne' (mul_right_cancel₀ h (key.symm.trans (one_mul _).symm))

theorem four_indicator (he : IsPair e) (L : AddSubgroup X) (ho : IsOpen (L : Set X)) (x : X) :
    four μ e ((L : Set X).indicator fun _ => (1 : ℂ)) x =
      (ann he L : Set X).indicator (fun _ => (μ.real (L : Set X) : ℂ)) x := by
  by_cases hx : x ∈ (ann he L : Set X)
  · rw [Set.indicator_of_mem hx]
    have hx' : ∀ y ∈ (L : Set X), e y x = 1 := hx
    simp only [four]
    have h : (fun z => e x z * (L : Set X).indicator (fun _ => (1 : ℂ)) z) =
        (L : Set X).indicator (fun _ => (1 : ℂ)) := by
      ext z
      by_cases hz : z ∈ (L : Set X)
      · rw [Set.indicator_of_mem hz, mul_one, he.symm, hx' z hz]
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [h, integral_indicator_const _ ho.measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    exact four_eq_zero μ he (indicator_invariant L 1) hx

private theorem exists_four_four_eq_smul_neg_of_ann_invariant (hX : Good X) (he : IsPair e) (L : AddSubgroup X)
    (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, (∀ t ∈ ann he (L : Set X), ∀ x, φ (x + t) = φ x) →
      ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  have := hX.sc
  set A := ann he (L : Set X) with hA
  set B := ann he (A : Set X) with hB
  have hAo : IsOpen (A : Set X) := isOpen_ann he hLc
  have hAc : IsCompact (A : Set X) := by
    obtain ⟨K, hK, hKA⟩ := he.big (L : Set X) (hLo.mem_nhds L.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen A hAo) fun y hy => hKA y hy
  have hBo : IsOpen (B : Set X) := isOpen_ann he hAc
  have hBc : IsCompact (B : Set X) := by
    obtain ⟨K, hK, hKB⟩ := he.big (A : Set X) (hAo.mem_nhds A.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen B hBo) fun y hy => hKB y hy
  have hLB : (L : Set X) ⊆ B := by
    intro z hz
    show ∀ y ∈ (A : Set X), e y z = 1
    intro y hy
    have hy' : ∀ x ∈ (L : Set X), e x y = 1 := hy
    rw [he.symm]
    exact hy' z hz
  have hBA : (ann he (B : Set X) : Set X) = A := by
    ext z
    constructor
    · intro hz
      have hz' : ∀ y ∈ (B : Set X), e y z = 1 := hz
      show ∀ x ∈ (L : Set X), e x z = 1
      exact fun x hx => hz' x (hLB hx)
    · intro hz
      show ∀ y ∈ (B : Set X), e y z = 1
      intro y hy
      have hy' : ∀ w ∈ (A : Set X), e w y = 1 := hy
      rw [he.symm]
      exact hy' z hz
  have hApos : 0 < μ.real (A : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
  have hBpos : 0 < μ.real (B : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne' hBc.measure_lt_top.ne
  refine ⟨μ.real (A : Set X) * μ.real (B : Set X), mul_pos hApos hBpos, fun φ hφ hs w => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hSc : IsCompact (tsupport φ) := hφ'.2.isCompact
  have : IsFiniteMeasure (μ.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSc.measure_lt_top⟩
  have : IsFiniteMeasure (μ.restrict (B : Set X)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBc.measure_lt_top⟩
  have h1 : ∀ x, ∫ z, e x z * φ z ∂μ = ∫ z in tsupport φ, e x z * φ z ∂μ := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]).symm
  have h2 : ∫ x, e w x * ∫ z, e x z * φ z ∂μ ∂μ = ∫ x in (B : Set X), e w x * ∫ z, e x z * φ z ∂μ ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have h0 := four_eq_zero μ he hs (y := x) hx
      simp only [four] at h0
      rw [h0, mul_zero]).symm
  have h3 : ∀ x, e w x * ∫ z in tsupport φ, e x z * φ z ∂μ =
      ∫ z in tsupport φ, e w x * (e x z * φ z) ∂μ := fun x => (integral_const_mul _ _).symm
  obtain ⟨C0, hC0⟩ := hφ'.1.continuous.bounded_above_of_compact_support hφ'.2
  have hcont : Continuous (Function.uncurry fun x z => e w x * (e x z * φ z)) :=
    (he.lc.continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (he.lc.continuous.mul (hφ'.1.continuous.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun x z => e w x * (e x z * φ z))
      ((μ.restrict (B : Set X)).prod (μ.restrict (tsupport φ))) :=
    (integrable_const C0).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simp only [Function.uncurry, norm_mul, he.norm, one_mul]
      exact hC0 p.2)
  have h4 : ∀ z, ∫ x in (B : Set X), e w x * (e x z * φ z) ∂μ =
      φ z * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    have hB1 := four_indicator μ he B hBo (w + z)
    simp only [four] at hB1
    rw [← hB1, ← integral_indicator hBo.measurableSet, mul_comm (φ z), ← integral_mul_const]
    congr 1
    ext x
    by_cases hx : x ∈ (B : Set X)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, he.add, he.symm z x]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      ring
  have h5 : ∀ z, φ z * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) =
      φ (-w) * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    by_cases hz : w + z ∈ (ann he (B : Set X) : Set X)
    · have hzA : w + z ∈ (A : Set X) := hBA.subset hz
      have h := hs (w + z) hzA (-w)
      rw [neg_add_cancel_left] at h
      rw [h]
    · rw [Set.indicator_of_notMem hz, mul_zero, mul_zero]
  have h6 : ∫ z in tsupport φ, φ (-w) * (ann he (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ =
      ∫ z, φ (-w) * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    rw [← h5 z, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hAm : MeasurableSet (ann he (B : Set X) : Set X) := by
    rw [hBA]
    exact hAo.measurableSet
  simp only [four]
  rw [h2]
  simp_rw [h1, h3]
  rw [integral_integral_swap hint]
  simp_rw [h4, h5]
  rw [h6, integral_const_mul,
    integral_add_left_eq_self (fun z => (ann he (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) z) w,
    integral_indicator_const _ hAm, hBA, Complex.real_smul]
  push_cast
  ring

theorem four_four_of_invariant (hX : Good X) (he : IsPair e) (M : AddSubgroup X) (hMc : IsCompact (M : Set X))
    (hMo : IsOpen (M : Set X)) : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, (∀ t ∈ M, ∀ x, φ (x + t) = φ x) →
      ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  obtain ⟨K, hK, hKM⟩ := he.small (M : Set X) (hMo.mem_nhds M.zero_mem)
  obtain ⟨L, hLc, hLo, hKL⟩ := hX.large K hK
  obtain ⟨C, hC, hCφ⟩ := exists_four_four_eq_smul_neg_of_ann_invariant μ hX he L hLc hLo
  refine ⟨C, hC, fun φ hφ hs => hCφ φ hφ fun t ht => hs t (hKM t fun x hx => ?_)⟩
  exact (show ∀ y ∈ (L : Set X), e y t = 1 from ht) x (hKL hx)

end GlobalTheory.KSp.FourInv

namespace GlobalTheory.KSp

open FourInv in

theorem four_four (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (hX : Good X)
    (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  have := hX.grp
  have := hX.t2
  obtain ⟨M0, hM0c, hM0o, -⟩ := hX.large ∅ isCompact_empty
  obtain ⟨C, hC, hCφ⟩ := four_four_of_invariant μ hX he M0 hM0c hM0o
  refine ⟨C, hC, fun φ hφ x => ?_⟩
  obtain ⟨U, hU, hUinv⟩ := exists_invariant hφ
  obtain ⟨M1, hM1c, hM1o, hM1U⟩ := hX.small U hU
  have hMo : IsOpen ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1o.inter hM0o
  have hMc : IsCompact ((M1 ⊓ M0 : AddSubgroup X) : Set X) := by
    rw [AddSubgroup.coe_inf]
    exact hM1c.inter_right (AddSubgroup.isClosed_of_isOpen M0 hM0o)
  obtain ⟨C', -, hC'φ⟩ := four_four_of_invariant μ hX he (M1 ⊓ M0) hMc hMo
  have h0 : (0 : X) ∈ (M0 : Set X) := M0.zero_mem
  have hCC : C' = C := by
    have h1 := hCφ _ (indicator_mem M0 hM0c hM0o) (indicator_invariant M0 1) 0
    have h2 := hC'φ _ (indicator_mem M0 hM0c hM0o)
      (fun t ht => indicator_invariant M0 1 t (AddSubgroup.mem_inf.mp ht).2) 0
    rw [neg_zero, Set.indicator_of_mem h0, mul_one] at h1 h2
    exact_mod_cast h2.symm.trans h1
  rw [← hCC]
  exact hC'φ φ hφ (fun t ht => hUinv M1 hM1U t (AddSubgroup.mem_inf.mp ht).1) x

end GlobalTheory.KSp

end
