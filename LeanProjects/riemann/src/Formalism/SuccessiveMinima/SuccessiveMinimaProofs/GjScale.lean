import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN
namespace GjScaling

def Zv (ι : Type*) : Set (ι → ℝ) := {k | ∀ i, ∃ m : ℤ, k i = m}

def Qv (ι : Type*) : Set (ι → ℝ) := {u | ∀ i, 0 ≤ u i ∧ u i < 1}

def tm {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) : ℝ≥0∞ := volume (Qv ι ∩ (B + Zv ι))

variable {ι : Type*} [Fintype ι]

lemma tm_mono {B B' : Set (ι → ℝ)} (h : B ⊆ B') : tm B ≤ tm B' := by
  unfold tm
  exact measure_mono (Set.inter_subset_inter subset_rfl (Set.add_subset_add h subset_rfl))

lemma tm_empty : tm (∅ : Set (ι → ℝ)) = 0 := by
  simp [tm]

lemma Zv_add {a b : ι → ℝ} (ha : a ∈ Zv ι) (hb : b ∈ Zv ι) : a + b ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  obtain ⟨m', hm'⟩ := hb i
  exact ⟨m + m', by rw [Pi.add_apply, hm, hm', Int.cast_add]⟩

lemma Zv_neg {a : ι → ℝ} (ha : a ∈ Zv ι) : -a ∈ Zv ι := fun i => by
  obtain ⟨m, hm⟩ := ha i
  exact ⟨-m, by rw [Pi.neg_apply, hm, Int.cast_neg]⟩

lemma mem_span_basisFun_iff (x : ι → ℝ) :
    x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ x ∈ Zv ι := by
  rw [Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom, Zv,
    Set.mem_setOf_eq]
  constructor
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩
  · intro h i
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, hm.symm⟩

lemma fundamentalDomain_eq : ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Qv ι := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, Pi.basisFun_repr, Set.mem_Ico, Qv, Set.mem_setOf_eq]

private theorem add_mem_add_intVectors_iff {T : Set (ι → ℝ)} {z : ι → ℝ} (hz : z ∈ Zv ι)
    (x : ι → ℝ) : z + x ∈ T + Zv ι ↔ x ∈ T + Zv ι := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hab' : a + b = z + x := hab
    refine ⟨a, ha, b + -z, Zv_add hb (Zv_neg hz), ?_⟩
    show a + (b + -z) = x
    rw [← add_assoc, hab', add_neg_cancel_comm]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, z + b, Zv_add hz hb, by
      show a + (z + b) = z + (a + b)
      exact add_left_comm a z b⟩

lemma tm_add_singleton {B : Set (ι → ℝ)} (hB : IsOpen B) (c : ι → ℝ) :
    tm (B + {c}) = tm B := by
  have hF : IsAddFundamentalDomain (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (Qv ι)
      volume := by
    rw [← fundamentalDomain_eq]
    exact ZSpan.isAddFundamentalDomain _ _
  have hF' := hF.vadd_of_comm c
  have hW : MeasurableSet (B + {c} + Zv ι) := hB.add_right.add_right.measurableSet
  have hinv : ∀ g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)),
      (fun x => g +ᵥ x) ⁻¹' (B + {c} + Zv ι) = B + {c} + Zv ι := fun g => by
    ext x
    exact add_mem_add_intVectors_iff ((mem_span_basisFun_iff _).1 g.2) x
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume := by
    refine ⟨?_⟩
    intro g s _
    exact measure_preimage_add volume (g : ι → ℝ) s
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    refine Function.Injective.countable
      (f := fun g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) => fun i => ⌊(g : ι → ℝ) i⌋) ?_
    intro g g' hgg
    apply Subtype.ext
    funext i
    obtain ⟨m, hm⟩ := (mem_span_basisFun_iff _).1 g.2 i
    obtain ⟨m', hm'⟩ := (mem_span_basisFun_iff _).1 g'.2 i
    have := congrFun hgg i
    simp only [hm, hm', Int.floor_intCast] at this
    rw [hm, hm', this]
  have h1 := hF.measure_set_eq hF' hW hinv
  have hshift : B + {c} + Zv ι = (fun x => c + x) '' (B + Zv ι) := by
    rw [add_comm B, add_assoc, Set.singleton_add]
  have h2 : (B + {c} + Zv ι) ∩ (c +ᵥ Qv ι) =
      (fun x => c + x) '' ((B + Zv ι) ∩ Qv ι) := by
    rw [Set.image_inter (add_right_injective c), ← hshift]
    rfl
  unfold tm
  rw [Set.inter_comm (Qv ι) (B + {c} + Zv ι), h1, h2, Set.image_add_left,
    measure_preimage_add, Set.inter_comm (B + Zv ι)]

lemma lintegral_scale {κ : Type*} [Fintype κ] (h : (κ → ℝ) → ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, h y = ENNReal.ofReal (s ^ Fintype.card κ) * ∫⁻ y, h (s • y) := by
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : ∫⁻ y, h (s • y) = ∫⁻ y, h y ∂(Measure.map (fun x : κ → ℝ => s • x) volume) :=
    (lintegral_map_equiv h (Homeomorph.smulOfNeZero s hs0).toMeasurableEquiv).symm
  rw [Measure.map_addHaar_smul (μ := volume) hs0, lintegral_smul_measure, smul_eq_mul,
    Module.finrank_fintype_fun_eq_card] at e1
  rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hs _).le, abs_of_pos (inv_pos.2 (pow_pos hs _)),
    mul_inv_cancel₀ (pow_ne_zero _ hs0), ENNReal.ofReal_one, one_mul]

section decomp
variable (n j : ℕ)

def emb (u : {i : Fin n // (i : ℕ) < j} → ℝ) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Fin n → ℝ :=
  fun i => if h : (i : ℕ) < j then u ⟨i, h⟩ else y ⟨i, h⟩

def fib (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Set ({i : Fin n // (i : ℕ) < j} → ℝ) :=
  {u | emb n j u y ∈ A}

lemma continuous_emb_left (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Continuous fun u => emb n j u y := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < j
  · simp only [emb, dif_pos h]
    exact continuous_apply _
  · simp only [emb, dif_neg h]
    exact continuous_const

lemma measurableSet_boxJ : MeasurableSet (boxJ n j) := by
  have : Formalism.FN.boxJ n j =
      ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < j), (fun u : Fin n → ℝ => u i) ⁻¹' Set.Ico 0 1 := by
    ext u
    simp [Formalism.FN.boxJ]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_pi_apply i measurableSet_Ico

lemma fib_set_eq (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    {u | emb n j u y ∈ boxJ n j ∩ (A + latJ n j)} = Qv _ ∩ (fib n j A y + Zv _) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hbox, a, ha, k, hk, hak⟩
    refine ⟨fun i => ?_, fun i => a i, ?_, fun i => k i, fun i => hk.1 i, ?_⟩
    · simpa only [emb, dif_pos i.2, Subtype.coe_eta] using hbox i.1 i.2
    · show emb n j (fun i => a i) y ∈ A
      convert ha using 1
      funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
      · have h := congrFun hak i
        simp only [emb, dif_neg hi, Pi.add_apply, hk.2 i (not_lt.mp hi), add_zero] at h
        simp only [emb, dif_neg hi, h]
    · funext i
      have h := congrFun hak i.1
      simp only [emb, dif_pos i.2, Pi.add_apply, Subtype.coe_eta] at h
      simpa only [Pi.add_apply] using h
  · rintro ⟨hcube, v, hv, w, hw, rfl⟩
    refine ⟨fun i hi => ?_, emb n j v y, hv, emb n j w 0,
      ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
    · simp only [emb, dif_pos hi]
      exact hcube ⟨i, hi⟩
    · by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi]
        exact hw ⟨i, hi⟩
      · exact ⟨0, by simp only [emb, dif_neg hi, Pi.zero_apply, Int.cast_zero]⟩
    · simp only [emb, dif_neg (not_lt.mpr hi), Pi.zero_apply]
    · funext i
      by_cases hi : (i : ℕ) < j
      · simp only [emb, dif_pos hi, Pi.add_apply]
      · simp only [emb, dif_neg hi, Pi.add_apply, Pi.zero_apply, add_zero]

private theorem measure_eq_of_measurePreserving_symm_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (S : Set α) :
    μ S = ν (e.symm ⁻¹' S) := by
  have h : Measure.map e μ (e.symm ⁻¹' S) = μ (e ⁻¹' (e.symm ⁻¹' S)) := e.map_apply _
  rw [he.map_eq] at h
  rw [h]
  congr 1
  ext x
  simp

lemma Gj_eq (A : Set (Fin n → ℝ)) (hA : IsOpen A) :
    Gj n j A = ∫⁻ y, tm (fib n j A y) := by
  have hS : MeasurableSet (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j)) :=
    (measurableSet_boxJ n j).inter hA.add_right.measurableSet
  have hmp := measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin n => (volume : Measure ℝ))
    (p := fun i : Fin n => (i : ℕ) < j)
  refine (measure_eq_of_measurePreserving_symm_preimage _ hmp
    (Formalism.FN.boxJ n j ∩ (A + Formalism.FN.latJ n j))).trans ?_
  rw [Measure.prod_apply_symm]
  · refine lintegral_congr fun y => ?_
    rw [tm, ← fib_set_eq]
    rfl
  · exact MeasurableEquiv.measurable _ hS

private theorem torusImageVolume_fib_le_smul {D : Set (Fin n → ℝ)} (hDo : IsOpen D)
    (hDc : Convex ℝ D) {s : ℝ} (hs : 1 ≤ s) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    tm (fib n j D y) ≤ tm (fib n j (s • D) (s • y)) := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le one_pos hs).ne'
  rcases (fib n j D y).eq_empty_or_nonempty with h | ⟨w, hw⟩
  · rw [h, tm_empty]
    exact zero_le
  have hopen : IsOpen (fib n j D y) := hDo.preimage (continuous_emb_left n j y)
  rw [← tm_add_singleton hopen ((s - 1) • w)]
  apply tm_mono
  rintro _ ⟨u, hu, c, hc, rfl⟩
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hu' : emb n j u y ∈ D := hu
  have hw' : emb n j w y ∈ D := hw
  show emb n j (u + (s - 1) • w) (s • y) ∈ s • D
  rw [Set.mem_smul_set]
  refine ⟨s⁻¹ • emb n j u y + (1 - s⁻¹) • emb n j w y,
    hDc hu' hw' (inv_nonneg.2 (by linarith)) ?_ (by ring), ?_⟩
  · nlinarith [mul_nonneg (inv_nonneg.2 (zero_le_one.trans hs)) (sub_nonneg.2 hs),
      inv_mul_cancel₀ hs0]
  · have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    funext i
    by_cases hi : (i : ℕ) < j
    · simp only [emb, dif_pos hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (u ⟨i, hi⟩ - w ⟨i, hi⟩) * hinv
    · simp only [emb, dif_neg hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

lemma card_compl (hj : j ≤ n) : Fintype.card {i : Fin n // ¬ (i : ℕ) < j} = n - j := by
  rw [← Fintype.card_fin (n - j)]
  exact Fintype.card_congr
    { toFun := fun i => ⟨(i.1 : ℕ) - j, by have := i.1.2; have := i.2; omega⟩
      invFun := fun k => ⟨⟨(k : ℕ) + j, by have := k.2; omega⟩, by
        show ¬ ((k : ℕ) + j < j); omega⟩
      left_inv := fun i => Subtype.ext (Fin.ext (by
        show (i.1 : ℕ) - j + j = i.1
        have := i.2
        omega))
      right_inv := fun k => Fin.ext (by
        show (k : ℕ) + j - j = k
        omega) }

end decomp
end GjScaling

open GjScaling in
theorem partialBoxVolumeScaling : GjScale := by
  intro n j C t t' hj hCo hCc _ _ ht htt'
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have hs : 0 < t' / t := div_pos ht' ht
  have hs1 : 1 ≤ t' / t := (le_div_iff₀ ht).2 (by linarith)
  have hD : IsOpen (t • C) := hCo.smul₀ ht.ne'
  have hDc : Convex ℝ (t • C) := hCc.smul t
  have hsD : t' • C = (t' / t) • (t • C) := by
    rw [smul_smul, div_mul_eq_mul_div, mul_div_assoc, div_self ht.ne', mul_one]
  have key := Formalism.FN.GjScaling.lintegral_scale
    (fun y => Formalism.FN.GjScaling.tm (Formalism.FN.GjScaling.fib n j ((t' / t) • (t • C)) y)) hs
  beta_reduce at key
  rw [Formalism.FN.GjScaling.card_compl n j hj] at key
  rw [hsD, Formalism.FN.GjScaling.Gj_eq n j _ hD,
    Formalism.FN.GjScaling.Gj_eq n j _ (hD.smul₀ hs.ne'), key]
  exact mul_le_mul_of_nonneg_left
    (lintegral_mono fun y => _root_.Formalism.FN.GjScaling.torusImageVolume_fib_le_smul n j hD hDc hs1 y) (by positivity)

end Formalism.FN
