import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHausdorffNullComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_lipschitzOnWith (x : E) (ℓ : E →L[ℝ] ℝ) {β δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun c => x + ((ℓ c - ℓ x) / β)⁻¹ • (c - x))
      {c | δ ≤ (ℓ c - ℓ x) / β ∧ ‖c - x‖ ≤ R} := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) ?_⟩
  rintro a ⟨ha, -⟩ b ⟨hb, hbR⟩
  set ta := (ℓ a - ℓ x) / β with hta_def
  set tb := (ℓ b - ℓ x) / β with htb_def
  have hta : 0 < ta := hδ.trans_le ha
  have htb : 0 < tb := hδ.trans_le hb
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [hta_def, div_zero] at hta
    exact lt_irrefl _ hta
  have hkey : x + ta⁻¹ • (a - x) - (x + tb⁻¹ • (b - x)) =
      ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x) := by
    simp only [smul_sub, sub_smul]; abel
  have hdiff : tb - ta = ℓ (b - a) / β := by
    rw [hta_def, htb_def, map_sub]; ring
  have hinv : |ta⁻¹ - tb⁻¹| ≤ ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) := by
    rw [inv_sub_inv hta.ne' htb.ne', hdiff, abs_div, abs_div, abs_of_pos (mul_pos hta htb), div_div]
    apply div_le_div₀ (by positivity)
    · rw [← Real.norm_eq_abs, norm_sub_rev a b]
      exact ℓ.le_opNorm _
    · exact mul_pos (abs_pos.2 hβ) (mul_pos hδ hδ)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hδ.le hta.le) (abs_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, hkey]
  calc ‖ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x)‖
      ≤ ‖ta⁻¹ • (a - b)‖ + ‖(ta⁻¹ - tb⁻¹) • (b - x)‖ := norm_add_le _ _
    _ = ta⁻¹ * ‖a - b‖ + |ta⁻¹ - tb⁻¹| * ‖b - x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hta)]
    _ ≤ δ⁻¹ * ‖a - b‖ + ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) * R := by
        gcongr
    _ = (δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) * ‖a - b‖ := by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem segment_hits_image_null {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {C : Set E} {x : E} (hx : x ∉ C) (ℓ : E →L[ℝ] ℝ) {α : ℝ}
    (hα : α ≠ ℓ x) (g : E →L[ℝ] F) {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] (g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty}) = 0 := by
  have hβ : α - ℓ x ≠ 0 := sub_ne_zero.2 hα
  have hsub : g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty} ⊆
      ⋃ j : ℕ, (g ∘ fun c => x + ((ℓ c - ℓ x) / (α - ℓ x))⁻¹ • (c - x)) ''
        (C ∩ {c | ((j : ℝ) + 1)⁻¹ ≤ (ℓ c - ℓ x) / (α - ℓ x) ∧ ‖c - x‖ ≤ (j : ℝ) + 1}) := by
    rintro _ ⟨m, ⟨hm, c, hcs, hcC⟩, rfl⟩
    rw [segment_eq_image'] at hcs
    obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hcs
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hcC
      exact hx hcC
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hτ : (ℓ (x + s • (m - x)) - ℓ x) / (α - ℓ x) = s := by
      rw [map_add, map_smul, map_sub, hm, smul_eq_mul, add_sub_cancel_left, mul_div_assoc,
        div_self hβ, mul_one]
    obtain ⟨j, hj⟩ := exists_nat_gt (max s⁻¹ ‖s • (m - x)‖)
    refine mem_iUnion.2 ⟨j, x + s • (m - x), ⟨hcC, ?_, ?_⟩, ?_⟩
    · rw [hτ]
      have h1 : s⁻¹ < (j : ℝ) + 1 := by linarith [le_max_left s⁻¹ ‖s • (m - x)‖]
      calc ((j : ℝ) + 1)⁻¹ ≤ (s⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hspos) h1.le
        _ = s := inv_inv s
    · rw [add_sub_cancel_left]
      linarith [le_max_right s⁻¹ ‖s • (m - x)‖]
    · simp only [Function.comp_apply, hτ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs,
        one_smul, add_sub_cancel]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  obtain ⟨K, hK⟩ := radial_lipschitzOnWith x ℓ (β := α - ℓ x) (R := (j : ℝ) + 1)
    (show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity)
  have hL := g.lipschitz.comp_lipschitzOnWith (hK.mono (inter_subset_right (s := C)))
  refine le_antisymm ?_ zero_le
  calc _ ≤ _ := hL.hausdorffMeasure_image_le hd
    _ = 0 := by rw [measure_mono_null inter_subset_left hC, mul_zero]

theorem diff_nonempty_of_hausdorffMeasure_null [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) : (U \ C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  obtain ⟨z, hz⟩ := hne
  have hlt : ((k : ℝ≥0) : ℝ≥0∞) < dimH U := by
    rw [Real.dimH_of_mem_nhds (hU.mem_nhds hz), hk]
    exact_mod_cast Nat.lt_succ_self k
  have htop := hausdorffMeasure_of_lt_dimH hlt
  rw [NNReal.coe_natCast, measure_mono_null h hC] at htop
  exact ENNReal.zero_ne_top htop

theorem convex_diff_isPreconnected [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {B : Set E}
    (hBo : IsOpen B) (hBc : Convex ℝ B) : IsPreconnected (B \ C) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  by_cases hxy : x = y
  · subst hxy
    exact ⟨{x}, singleton_subset_iff.2 hx, rfl, rfl, isPreconnected_singleton⟩
  let φ : E ≃L[ℝ] (Fin (k + 1) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hk, Module.finrank_fin_fun])
  obtain ⟨i, hi⟩ : ∃ i, φ x i ≠ φ y i := by
    by_contra h
    push Not at h
    exact hxy (φ.injective (funext h))
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  let g : E →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)).comp
      (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  have hℓ : ∀ z, ℓ z = φ z i := fun z => rfl
  have hg : ∀ z, g z = Fin.removeNth i (φ z) := fun z => rfl
  have hαx : (φ x i + φ y i) / 2 ≠ ℓ x := by rw [hℓ]; intro h; apply hi; linarith
  have hαy : (φ x i + φ y i) / 2 ≠ ℓ y := by rw [hℓ]; intro h; apply hi; linarith
  have hvol : (volume : Measure (Fin k → ℝ)) = μH[(k : ℝ)] := by
    have := hausdorffMeasure_pi_real (ι := Fin k)
    rw [Fintype.card_fin] at this
    exact this.symm
  have hS0 : volume (g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ x m ∩ C).Nonempty} ∪
      g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ y m ∩ C).Nonempty}) = 0 := by
    rw [hvol]
    exact measure_union_null (segment_hits_image_null hx.2 ℓ hαx g (Nat.cast_nonneg k) hC)
      (segment_hits_image_null hy.2 ℓ hαy g (Nat.cast_nonneg k) hC)
  let ψ : (Fin k → ℝ) → E := fun w => φ.symm (Fin.insertNth i ((φ x i + φ y i) / 2) w)
  have hψc : Continuous ψ :=
    φ.symm.continuous.comp (continuous_const.finInsertNth i continuous_id)
  have hz₀ : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ B :=
    hBc hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hψz₀ : ψ (g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    have h1 : φ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i = (φ x i + φ y i) / 2 := by
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp only [ψ, hg]
    rw [← h1, Fin.insertNth_self_removeNth, ContinuousLinearEquiv.symm_apply_apply]
  have hWpos : 0 < volume (ψ ⁻¹' B) :=
    (hBo.preimage hψc).measure_pos volume ⟨_, show ψ _ ∈ B from hψz₀ ▸ hz₀⟩
  obtain ⟨w, hwB, hwS⟩ := nonempty_of_measure_ne_zero
    ((measure_sdiff_null hS0).symm ▸ hWpos.ne' : volume (ψ ⁻¹' B \ _) ≠ 0)
  have hφm : φ (ψ w) = Fin.insertNth i ((φ x i + φ y i) / 2) w := by
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply]
  have hℓm : ℓ (ψ w) = (φ x i + φ y i) / 2 := by rw [hℓ, hφm, Fin.insertNth_apply_same]
  have hgm : g (ψ w) = w := by rw [hg, hφm, Fin.removeNth_insertNth]
  have hxm : segment ℝ x (ψ w) ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hx.1 hwB hc, fun hcC => hwS (Or.inl ⟨ψ w, ⟨hℓm, c, hc, hcC⟩, hgm⟩)⟩
  have hmy : segment ℝ (ψ w) y ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hwB hy.1 hc, fun hcC =>
      hwS (Or.inr ⟨ψ w, ⟨hℓm, c, segment_symm ℝ (ψ w) y ▸ hc, hcC⟩, hgm⟩)⟩
  exact ⟨segment ℝ x (ψ w) ∪ segment ℝ (ψ w) y, union_subset hxm hmy,
    Or.inl (left_mem_segment ℝ x (ψ w)), Or.inr (right_mem_segment ℝ (ψ w) y),
    (convex_segment x (ψ w)).isPreconnected.union (ψ w) (right_mem_segment ℝ x (ψ w))
      (left_mem_segment ℝ (ψ w) y) (convex_segment (ψ w) y).isPreconnected⟩

theorem HausdorffNullComplementConnected.proof : HausdorffNullComplementConnected.Statement := by
  intro E _ _ _ _ _ D C hDo hDc hC
  by_cases h0 : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact Set.subsingleton_of_subsingleton.isPreconnected
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h0
  have hC' : μH[(k : ℝ)] C = 0 := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hC
    exact hC
  choose! r hr0 hrD using Metric.isOpen_iff.1 hDo
  have hU : D \ C = ⋃ z ∈ D, ball z (r z) \ C := by
    ext z
    simp only [mem_sdiff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨z, hz, mem_ball_self (hr0 z hz), hzC⟩
    · rintro ⟨w, hw, hzb, hzC⟩
      exact ⟨hrD w hw hzb, hzC⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun z _ => convex_diff_isPreconnected hk hC' isOpen_ball (convex_ball z (r z))) ?_
  intro z hz w hw
  refine hDc.induction₂' (fun a b => ReflTransGen
      (fun i j => ((ball i (r i) \ C) ∩ (ball j (r j) \ C)).Nonempty ∧ i ∈ D) a b) ?_
    (fun a b c _ _ _ h1 h2 => h1.trans h2) hz hw
  intro a ha
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (hr0 a ha)), self_mem_nhdsWithin]
    with b hb hbD
  obtain ⟨p, ⟨hpa, hpb⟩, hpC⟩ := diff_nonempty_of_hausdorffMeasure_null hk hC'
    (isOpen_ball.inter isOpen_ball) ⟨b, hb, mem_ball_self (hr0 b hbD)⟩
  exact ⟨ReflTransGen.single ⟨⟨p, ⟨hpa, hpC⟩, hpb, hpC⟩, ha⟩,
    ReflTransGen.single ⟨⟨p, ⟨hpb, hpC⟩, hpa, hpC⟩, hbD⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
