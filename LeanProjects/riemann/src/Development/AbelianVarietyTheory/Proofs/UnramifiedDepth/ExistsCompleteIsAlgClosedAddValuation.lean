import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteSiteAlg

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.DvrClosedEmbedding

theorem exists_addValuation_log_norm {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ v : AddValuation C (WithTop ℝ),
      (∀ x, x ≠ 0 → v x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)) ∧
      ∀ (x : C) (n : ℕ), (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v x ↔ ‖x‖ ≤ r ^ n := by
  classical
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  let f : C → WithTop ℝ := fun x =>
    if x = 0 then ⊤ else ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)
  have hf0 : f 0 = ⊤ := by simp [f]
  have hf : ∀ x, x ≠ 0 → f x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ) := fun x hx => by
    simp [f, hx]
  have hmono : ∀ x y : C, ‖x‖ ≤ ‖y‖ → f y ≤ f x := by
    intro x y h
    by_cases hx : x = 0
    · rw [hx, hf0]; exact le_top
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : y ≠ 0 := norm_pos_iff.1 (hx'.trans_le h)
    rw [hf x hx, hf y hy, WithTop.coe_le_coe]
    exact div_le_div_of_nonpos_of_le hl.le (Real.log_le_log hx' h)
  refine ⟨AddValuation.of f hf0 ?_ ?_ ?_, hf, ?_⟩
  · rw [hf 1 one_ne_zero]; simp
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y) with h | h
    · exact min_le_of_left_le (hmono _ _ h)
    · exact min_le_of_right_le (hmono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, zero_mul, hf0, WithTop.top_add]
    by_cases hy : y = 0
    · rw [hy, mul_zero, hf0, WithTop.add_top]
    rw [hf x hx, hf y hy, hf _ (mul_ne_zero hx hy), norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div, WithTop.coe_add]
  · intro x n
    change _ ≤ f x ↔ _
    by_cases hx : x = 0
    · rw [hx, hf0, norm_zero]
      exact ⟨fun _ => by positivity, fun _ => le_top⟩
    rw [hf x hx, WithTop.coe_le_coe, le_div_iff_of_neg hl, ← Real.log_pow,
      Real.log_le_log_iff (norm_pos_iff.2 hx) (pow_pos hr0 n)]

theorem exists_limit_of_norm_sub_le_pow {C : Type} [NormedField C] [IsUltrametricDist C]
    [CompleteSpace C] {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℕ → C)
    (hs : ∀ n, ‖s (n + 1) - s n‖ ≤ r ^ n) : ∃ x, ∀ n, ‖x - s n‖ ≤ r ^ n := by
  have hc : CauchySeq s := by
    refine cauchySeq_of_le_geometric r 1 hr1 fun n => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact hs n
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, fun n => ?_⟩
  refine le_of_tendsto ((hL.sub tendsto_const_nhds).norm) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  induction m, hm using Nat.le_induction with
  | base => simp; positivity
  | succ m hm ih =>
    have h := IsUltrametricDist.norm_add_le_max (s (m + 1) - s m) (s m - s n)
    rw [sub_add_sub_cancel] at h
    exact h.trans (max_le ((hs m).trans (pow_le_pow_of_le_one hr0.le hr1.le hm)) ih)

theorem exists_complete_isAlgClosed_addValuation :
    ∀ (T : CDVR) (p : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C), v (p : C) = 1 ∧ (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) ∧ IsAlgClosed C ∧ ∀ s : ℕ → C, (∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (x - s n) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  obtain ⟨v, hv, hvn⟩ := exists_addValuation_log_norm (C := C) hr0 hr1
  have hl : Real.log (1 / 2) ≠ 0 := (Real.log_neg hr0 hr1).ne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hz : ∀ x : T.Fr, x ≠ 0 → Real.log ‖algebraMap T.Fr C x‖ =
      (vV T.V x : ℝ) * Real.log ‖algebraMap T.Fr C (algebraMap T.V T.Fr π)‖ := fun x hx => by
    rw [ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) (fun a => (hC _).2 ⟨a, rfl⟩) hπ hx,
      Real.log_zpow]
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hzp := hz p hpF
  rw [hCp] at hzp
  refine ⟨C, inferInstance, inferInstance, v, algebraMap T.Fr C, ?_, fun x hx => ?_,
    inferInstance, fun s hs => ?_⟩
  · rw [map_natCast] at hCp
    rw [hv _ (Nat.cast_ne_zero.2 hp.ne_zero), hCp, div_self hl, WithTop.coe_one]
  · rw [hv _ ((map_ne_zero _).2 hx), hz x hx, hzp,
      mul_div_mul_right _ _ (right_ne_zero_of_mul (hzp ▸ hl))]
  · obtain ⟨x, hx⟩ := exists_limit_of_norm_sub_le_pow hr0 hr1 s fun n => (hvn _ n).1 (hs n)
    exact ⟨x, fun n => (hvn _ n).2 (hx n)⟩

end GlobalTheory.DvrClosedEmbedding
