import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsVerticalCartier
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Homog

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_C (c : ℤ) : IsMultiHomog (C c : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isMultiHomog_prod {σ : Type} (s : Finset σ) (f : σ → MRing ι) (d : σ → κ → ℕ)
    (h : ∀ a ∈ s, IsMultiHomog (f a) (d a)) : IsMultiHomog (∏ a ∈ s, f a) (∑ a ∈ s, d a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ProjLine.isMultiHomog_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ProjLine.mhMul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem isMultiHomog_chartMonomial (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have h := isMultiHomog_prod (Finset.univ : Finset κ) (fun k => (X ⟨k, c k⟩ : MRing ι))
    (fun k => fun k1 => if k1 = k then 1 else 0) (fun k _ => ProjLine.isMultiHomog_X ⟨k, c k⟩)
  have hs : (∑ k : κ, (fun k1 : κ => if k1 = k then 1 else 0 : κ → ℕ)) = fun _ => 1 := by
    funext k1
    simp [Finset.sum_apply]
  rwa [hs] at h

end Homog

section Values

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem mem_mCoordIdeal_of_aeval {f : MRing ι} {d : κ → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

theorem IsValueAt.unique {a : Ω} {v v' : ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (h : IsValueAt y a z v) (h' : IsValueAt y a z v') : v = v' := by
  obtain ⟨d, g, h1, hg, hh, hy, hyg, hz1, hzg⟩ := h
  obtain ⟨d', g', h1', hg', hh', hy', hyg', hz1', hzg'⟩ := h'
  have hm : IsMultiHomog (g * h1' - g' * h1) (d + d') := by
    rw [sub_eq_add_neg]
    refine ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg ?_)
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  have h0 : aeval y (g * h1' - g' * h1) = 0 := by
    rw [map_sub, map_mul, map_mul, hyg, hyg']
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval hm h0)
  rw [map_sub, map_mul, map_mul, eval_sub, eval_mul, eval_mul, hzg, hzg', sub_eq_zero] at hz0
  have hne : eval z (map (Int.castRingHom ℂ) h1) * eval z (map (Int.castRingHom ℂ) h1') ≠ 0 :=
    mul_ne_zero hz1 hz1'
  apply mul_right_cancel₀ hne
  linear_combination hz0

theorem valAt_eq {a : Ω} {v : ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (h : IsValueAt y a z v) :
    valAt y a z = v := by
  have hr : RegularAt y a z := ⟨v, h⟩
  rw [valAt, dif_pos hr]
  exact IsValueAt.unique hz hr.choose_spec h

theorem RegularAt.isValueAt {a : Ω} (hz : z ∈ mcPts (mCoordIdeal y)) (h : RegularAt y a z) :
    IsValueAt y a z (valAt y a z) := by
  obtain ⟨v, hv⟩ := h
  rwa [valAt_eq hz hv]

theorem IsValueAt.mul {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a * b) z (v * w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  refine ⟨d + d', g * g', h * h', ProjLine.mhMul hg hg', ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_mul, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.add {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a + b) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  have hd : IsMultiHomog (g' * h) (d + d') := by
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  refine ⟨d + d', g * h' + g' * h, h * h', ProjLine.mhAdd (ProjLine.mhMul hg hh') hd,
    ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_add, map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add, map_mul, eval_add, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.neg {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) : IsValueAt y (-a) z (-v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hy, ?_, hz, ?_⟩
  · rw [map_neg, hyg]
    ring
  · rw [map_neg, eval_neg, hzg]
    ring

theorem isValueAt_intCast (n : ℤ) : IsValueAt y (n : Ω) z (n : ℂ) := by
  refine ⟨0, C n, 1, isMultiHomog_C n, ProjLine.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_one : IsValueAt y (1 : Ω) z 1 := by
  simpa using isValueAt_intCast (y := y) (z := z) 1

theorem isValueAt_zero : IsValueAt y (0 : Ω) z 0 := by
  simpa using isValueAt_intCast (y := y) (z := z) 0

theorem IsValueAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} {v : σ → ℂ}
    (h : ∀ i ∈ s, IsValueAt y (a i) z (v i)) : IsValueAt y (∑ i ∈ s, a i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem RegularAt.mul {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a * b) z :=
  ⟨_, ha.choose_spec.mul hb.choose_spec⟩

theorem RegularAt.add {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a + b) z :=
  ⟨_, ha.choose_spec.add hb.choose_spec⟩

theorem RegularAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} (h : ∀ i ∈ s, RegularAt y (a i) z) :
    RegularAt y (∑ i ∈ s, a i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using isValueAt_zero⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype κ] [∀ k, Fintype (ι k)] in

theorem eval_conj (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => starRingEnd ℂ (z p)) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem IsValueAt.conj {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_conj]
    exact (map_ne_zero _).2 hz
  · rw [eval_conj, eval_conj, hzg, map_mul]

theorem IsValueAt.smul {a : Ω} {v : ℂ} (s : κ → ℂ) (hs : ∀ k, s k ≠ 0) (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => s p.1 * z p) v := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)) hz
  · rw [eval_smul_homog h d hh, eval_smul_homog g d hg, hzg]
    ring

theorem regularAt_of_mem_chartRing (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ chartRing ℤ (NumbersDVR.segreVec y) c) :
    RegularAt y a z := by
  have hden : NumbersDVR.segreVec y c ≠ 0 := by
    intro h0
    have hm := mem_mCoordIdeal_of_aeval (y := y) (isMultiHomog_chartMonomial c)
      (by simpa [NumbersDVR.segreVec] using h0)
    have := hz.2 _ hm
    simp only [map_prod, map_X, eval_prod, eval_X] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    have hz0 : eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))) ≠ 0 := by
      simp only [map_prod, map_X, eval_prod, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    refine ⟨eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c' k⟩ : MRing ι))) /
      eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))), fun _ => 1,
      ∏ k, (X ⟨k, c' k⟩ : MRing ι), ∏ k, (X ⟨k, c k⟩ : MRing ι), isMultiHomog_chartMonomial c',
      isMultiHomog_chartMonomial c, ?_, ?_, hz0, ?_⟩
    · simpa [NumbersDVR.segreVec] using hden
    · simp only [map_prod, aeval_X]
      show NumbersDVR.segreVec y c' = NumbersDVR.segreVec y c' / NumbersDVR.segreVec y c *
        NumbersDVR.segreVec y c
      rw [div_mul_cancel₀ _ hden]
    · rw [div_mul_cancel₀ _ hz0]
  | algebraMap r =>
    exact ⟨r, by simpa using isValueAt_intCast (y := y) (z := z) r⟩
  | add a b _ _ ha hb => exact ha.add hb
  | mul a b _ _ ha hb => exact ha.mul hb

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
