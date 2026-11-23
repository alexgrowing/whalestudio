import Mathlib

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped ENNReal
open MeasureTheory

theorem oneD (u u' : ℝ → ℂ) (hu' : Continuous u') (h : ∀ t, HasDerivAt u (u' t) t) :
    ‖u 0‖ₑ ^ 2 ≤ 2 * ∫⁻ t, (‖u t‖ₑ ^ 2 + ‖u' t‖ₑ ^ 2) := by
  have hu : Continuous u := continuous_iff_continuousAt.2 fun t => (h t).continuousAt
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((s : ℂ) - 1) * u s ^ 2) (u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) - 1) 1 t := (Complex.ofRealCLM.hasDerivAt (x := t)).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => u s ^ 2) (2 * u t * u' t) t := by
      simpa using (h t).fun_pow 2
    simpa using h1.fun_mul h2
  have hc : Continuous fun t : ℝ => u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t) := by fun_prop
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at e
  have e' : u 0 ^ 2 = ∫ t in Set.Ioc (0 : ℝ) 1, (u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)) := by
    rw [e]; simp
  rw [← enorm_pow, e', ← lintegral_const_mul' _ _ (by simp)]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_) (setLIntegral_le_lintegral _ _)
  have h1 : ‖(t : ℂ) - 1‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : ‖u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)‖ ≤ 2 * (‖u t‖ ^ 2 + ‖u' t‖ ^ 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_two]
    have : ‖(t : ℂ) - 1‖ * (2 * ‖u t‖ * ‖u' t‖) ≤ 1 * (2 * ‖u t‖ * ‖u' t‖) := by gcongr
    nlinarith [sq_nonneg (‖u t‖ - ‖u' t‖), sq_nonneg ‖u' t‖]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal h2

theorem lintegral_fin_succ {D : ℕ} (G : (Fin (D + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ t, G t = ∫⁻ s : ℝ, ∫⁻ t : Fin D → ℝ, G (Fin.cons s t) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℝ) 0).symm
  rw [← hp.lintegral_comp hG, Measure.volume_eq_prod,
    lintegral_prod (fun a => G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℝ) 0).symm a))
      (hG.comp (MeasurableEquiv.measurable _)).aemeasurable]
  refine lintegral_congr fun s => lintegral_congr fun t => congrArg G ?_
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def sumSq (dd : W → (X → ℂ) → X → ℂ) (L : List (List W)) (Θ : X → ℂ) (y : X) : ℝ≥0∞ :=
  (L.map fun l => ‖l.foldr dd Θ y‖ₑ ^ 2).sum

omit [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] in
theorem foldr_mem {S : Set (X → ℂ)} {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (l : List W) {Θ : X → ℂ}
    (h : Θ ∈ S) : l.foldr dd Θ ∈ S := by
  induction l with
  | nil => exact h
  | cons w l ih => exact hd w _ ih

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
theorem continuous_sumSq {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) : Continuous (sumSq dd L Θ) :=
  continuous_list_sum L fun l _ => (ENNReal.continuous_pow 2).comp (hS _ (foldr_mem hd l h)).enorm

theorem sobAbs {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (D : ℕ) : ∀ (ws : Fin D → W) (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) →
      (∀ i, ∀ Θ ∈ S, ∀ x, HasDerivAt (fun t => Θ (x + e i t)) (dd (ws i) Θ x) 0) →
      ∃ L : List (List W), ∀ Θ ∈ S, ∀ x, ‖Θ x‖ₑ ^ 2 ≤ 2 ^ D * ∫⁻ t : Fin D → ℝ, sumSq dd L Θ (x + ∑ i, e i (t i)) := by
  induction D with
  | zero =>
    intro ws e _ _
    refine ⟨[[]], fun Θ _ x => ?_⟩
    simp [sumSq, volume_pi]
  | succ D ih =>
    intro ws e he hder
    obtain ⟨L, hL⟩ := ih (fun i => ws i.succ) (fun i => e i.succ) (fun i => he _) (fun i => hder _)
    refine ⟨L ++ L.map (· ++ [ws 0]), fun Θ hΘ x => ?_⟩
    have hΘ' := hd (ws 0) Θ hΘ
    have hline : Continuous fun s => x + e 0 s := continuous_const.add (he 0)
    have h1 := oneD (fun s => Θ (x + e 0 s)) (fun s => dd (ws 0) Θ (x + e 0 s)) ((hS _ hΘ').comp hline) fun t => by
      have h := hder 0 Θ hΘ (x + e 0 t)
      have h' : HasDerivAt (fun r => Θ (x + e 0 t + e 0 r)) (dd (ws 0) Θ (x + e 0 t)) (t - t) := by rwa [sub_self]
      have h'' := h'.comp_sub_const t t
      refine h''.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      simp only [map_sub]
      congr 1
      abel
    simp only [map_zero, add_zero] at h1
    have hsum : ∀ y, sumSq dd (L ++ L.map (· ++ [ws 0])) Θ y = sumSq dd L Θ y + sumSq dd L (dd (ws 0) Θ) y := fun y => by
      simp [sumSq, List.map_map, Function.comp_def, List.foldr_append]
    have hc : ∀ {D : ℕ} (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) → ∀ x : X,
        Continuous fun t : Fin D → ℝ => x + ∑ i, e i (t i) := fun e he x =>
      continuous_const.add (continuous_finsetSum _ fun i _ => (he i).comp (continuous_apply i))
    have hm : ∀ {D : ℕ} (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) → ∀ (x : X) (L : List (List W)),
        Measurable fun t : Fin D → ℝ => sumSq dd L Θ (x + ∑ i, e i (t i)) := fun e he x L =>
      ((continuous_sumSq hS hd L hΘ).comp (hc e he x)).measurable
    rw [lintegral_fin_succ _ (hm e he x _)]
    refine h1.trans ?_
    rw [pow_succ', mul_assoc]
    gcongr
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun s => ?_
    refine (add_le_add (hL Θ hΘ _) (hL _ hΘ' _)).trans (le_of_eq ?_)
    rw [← mul_add, ← lintegral_add_left (hm (fun i => e i.succ) (fun i => he _) _ _)]
    congr 1
    refine lintegral_congr fun t => ?_
    simp only [hsum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
theorem lintegral_sumSq [MeasurableSpace X] [BorelSpace X] (μ : Measure X) {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ)
    {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) :
    ∫⁻ y, sumSq dd L Θ y ∂μ = (L.map fun l => ∫⁻ y, ‖l.foldr dd Θ y‖ₑ ^ 2 ∂μ).sum := by
  induction L with
  | nil => simp [sumSq]
  | cons l L ih =>
    rw [List.map_cons, List.sum_cons, ← ih,
      ← lintegral_add_left ((hS _ (foldr_mem hd l h)).measurable.enorm.pow_const 2)]
    rfl

end PositivityTheory.ThKF0.Grow
