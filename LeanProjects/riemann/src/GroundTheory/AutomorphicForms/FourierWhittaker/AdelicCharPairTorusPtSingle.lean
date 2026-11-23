import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.AlgebraMapIntegerMemIntegralFiniteAdeles

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain
  Module
open scoped NumberField.AdeleRing FourierTransform Real

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

theorem exists_bound_of_periodic {f : (ι → 𝔸[K]) → ℂ} (hc : Continuous f)
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_vecDomain (K := K) (ι := ι)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨g, hg, -⟩ := existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) x
  rw [← hper g g.2 x]
  exact hM _ (hDC hg)

theorem ofCoord_zero : ofCoord (0 : BIdx K → ℝ) = 0 := by
  have := ofCoord_add (K := K) 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem torusPt_add (s t : ι × BIdx K → ℝ) : torusPt (s + t) = torusPt s + torusPt (K := K) t := by
  funext i
  simp only [torusPt, Pi.add_apply]
  rw [show (fun j => s (i, j) + t (i, j)) = (fun j => s (i, j)) + fun j => t (i, j) from rfl,
    ofCoord_add, map_add]

def tau (ξ : ι → K) (p : ι × BIdx K) : ℝ := (Algebra.trace ℚ K (ξ p.1 * integralBasis K p.2) : ℝ)

theorem adelicChar_pair_torusPt_single [DecidableEq ι] (ξ : ι → K) (p : ι × BIdx K) (s : ℝ) :
    GroundTheory.Global.adelicChar K (pair ξ (torusPt (Pi.single p s))) = 𝐞 (-(s * tau ξ p)) := by
  classical
  rw [pair_torusPt]
  have := GroundTheory.Global.adelicChar_infinite (K := K)
    (∑ i, algebraMap K (InfiniteAdeleRing K) (ξ i) * ofCoord fun j => (Pi.single p s : ι × BIdx K → ℝ) (i, j))
  refine this.trans ?_
  congr 2
  rw [map_sum]
  simp_rw [infiniteTrace_algebraMap_mul_ofCoord]
  rw [← Fintype.sum_prod_type (f := fun q : ι × BIdx K =>
    (Pi.single p s : ι × BIdx K → ℝ) q * (Algebra.trace ℚ K (ξ q.1 * integralBasis K q.2) : ℝ))]
  rw [Finset.sum_eq_single p]
  · simp [tau]
  · intro q _ hq
    simp [Pi.single_eq_of_ne hq]
  · simp

theorem hasDerivAt_fourierChar_neg_mul (τ : ℝ) :
    HasDerivAt (fun s : ℝ => (𝐞 (-(s * τ)) : ℂ)) (-2 * π * Complex.I * τ) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => ((2 * π * (-(s * τ)) : ℝ) : ℂ) * Complex.I)
      ((((2 * π * (-τ)) : ℝ) : ℂ) * Complex.I) 0 := by
    have : HasDerivAt (fun s : ℝ => (2 * π * (-(s * τ)) : ℝ)) (2 * π * (-τ)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const τ).neg.const_mul (2 * π)
      simpa using this
    exact this.ofReal_comp.mul_const Complex.I
  have h2 := h1.cexp
  simp only [Real.fourierChar_apply] at h2 ⊢
  convert h2 using 1
  simp only [mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  push_cast
  ring

theorem vecCoeff_deriv [DecidableEq ι] {f f' : (ι → 𝔸[K]) → ℂ} (hf : Continuous f)
    (hfper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) (hf' : Continuous f')
    (hf'per : ∀ ξ ∈ vecLattice K ι, ∀ x, f' (ξ + x) = f' x) (p : ι × BIdx K)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => f (x + torusPt (Pi.single p s))) (f' x) 0) (ξ : ι → K) :
    vecCoeff f' ξ = -2 * π * Complex.I * tau ξ p * vecCoeff f ξ := by
  set a : ℝ → ι → 𝔸[K] := fun s => torusPt (Pi.single p s)
  have ha : ∀ s r, a (s + r) = a s + a r := fun s r => by
    simp only [a, Pi.single_add, torusPt_add]
  set χ : (ι → 𝔸[K]) → ℂ := fun x => (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ)
  have hχ : Continuous χ := continuous_adelicChar_neg_pair ξ
  obtain ⟨C, hC⟩ := exists_bound_of_periodic hf' hf'per
  set μ := (vecMeasure K ι).restrict (vecDomain K ι)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hcont_a : Continuous a := continuous_torusPt.comp (continuous_pi fun q => by
    by_cases h : q = p
    · subst h; simp only [Pi.single_eq_same]; exact continuous_id
    · simp only [Pi.single_eq_of_ne h]; exact continuous_const)

  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s x => f (x + a s) * χ x) (F' := fun s x => f' (x + a s) * χ x)
    (bound := fun _ => C) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun s => ((hf.comp (continuous_id.add continuous_const)).mul hχ).aestronglyMeasurable)
    (((hf.comp (continuous_id.add continuous_const)).mul hχ).continuousOn.integrableOn_compact
      isCompact_closure_vecDomain |>.mono_set subset_closure)
    ((hf'.comp (continuous_id.add continuous_const)).mul hχ).aestronglyMeasurable
    (ae_of_all _ fun x s _ => by
      simp only [norm_mul, χ, Circle.norm_coe, mul_one]; exact hC _)
    (integrable_const C)
    (ae_of_all _ fun x s _ => by
      have h0 : HasDerivAt (fun r : ℝ => f (x + a s + torusPt (Pi.single p r))) (f' (x + a s))
          (s + -s) := by rw [add_neg_cancel]; exact hd (x + a s)
      have h1 := h0.comp_add_const s (-s)
      have h2 : (fun r : ℝ => f (x + a s + torusPt (Pi.single p (r + -s)))) =
          fun r => f (x + a r) := by
        funext r
        change f (x + a s + a (r + -s)) = f (x + a r)
        rw [add_assoc, ← ha]
        congr 3
        ring
      rw [h2] at h1
      exact h1.mul_const (χ x))
  have ha0 : a 0 = 0 := by
    funext i
    simp only [a, Pi.single_zero, torusPt, Pi.zero_apply]
    rw [show (fun _ : BIdx K => (0 : ℝ)) = 0 from rfl, ofCoord_zero, map_zero]
  have hL : HasDerivAt (fun s => vecCoeff (fun x => f (x + a s)) ξ) (vecCoeff f' ξ) 0 := by
    have := hmain.2
    simp only [ha0, add_zero] at this
    exact this
  have hR : HasDerivAt (fun s => vecCoeff (fun x => f (x + a s)) ξ)
      (-2 * π * Complex.I * tau ξ p * vecCoeff f ξ) 0 := by
    have e : (fun s => vecCoeff (fun x => f (x + a s)) ξ) =
        fun s => (𝐞 (-(s * tau ξ p)) : ℂ) * vecCoeff f ξ := by
      funext s
      rw [vecCoeff_translate hfper, adelicChar_pair_torusPt_single]
    rw [e]
    exact (hasDerivAt_fourierChar_neg_mul _).mul_const _
  exact hL.unique hR

theorem summable_pi_prod {P : Type*} [Fintype P] {g : ℤ → ℝ} (hg : Summable g) (hg0 : 0 ≤ g) :
    Summable fun n : P → ℤ => ∏ p, g (n p) := by
  classical
  suffices h : ∀ m : ℕ, Summable fun n : Fin m → ℤ => ∏ i, g (n i) by
    let e := Fintype.equivFin P
    have hs := ((e.arrowCongr (Equiv.refl ℤ)).summable_iff).2 (h (Fintype.card P))
    refine hs.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.arrowCongr_apply, Equiv.coe_refl]
    exact Fintype.prod_equiv e.symm _ _ fun i => rfl
  intro m
  induction m with
  | zero => exact (hasSum_fintype _).summable
  | succ m ih =>
    have h2 := Summable.mul_of_nonneg hg ih hg0 (fun n => Finset.prod_nonneg fun i _ => hg0 _)
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ℤ).summable_iff]
    refine h2.congr fun q => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_inv_one_add_sq : Summable fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2) := by
  have h1 : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 one_lt_two
  have h2 : Summable fun n : ℤ => (Pi.single 0 1 : ℤ → ℝ) n :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [Pi.single_eq_of_ne hn]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h1.add h2)
  by_cases hn : n = 0
  · subst hn; simp
  · have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    simp only [Pi.single_eq_of_ne hn, add_zero]
    exact one_div_le_one_div_of_le hn' (by linarith)

theorem vecCoeff_iterDeriv [DecidableEq ι] (F : List (ι × BIdx K) → (ι → 𝔸[K]) → ℂ)
    (hc : ∀ l, Continuous (F l)) (hper : ∀ l, ∀ ξ ∈ vecLattice K ι, ∀ x, F l (ξ + x) = F l x)
    (hd : ∀ l p x, HasDerivAt (fun s : ℝ => F l (x + torusPt (Pi.single p s))) (F (p :: l) x) 0)
    (l : List (ι × BIdx K)) (ξ : ι → K) :
    vecCoeff (F l) ξ = (l.map fun p => -2 * π * Complex.I * tau ξ p).prod * vecCoeff (F []) ξ := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [vecCoeff_deriv (hc l) (hper l) (hc (p :: l)) (hper (p :: l)) p (hd l p), ih,
      List.map_cons, List.prod_cons]
    ring

theorem prod_map_flatMap_pair {M : Type*} [CommMonoid M] (l : List (ι × BIdx K))
    (g : ι × BIdx K → M) :
    ((l.flatMap fun p => [p, p]).map g).prod = (l.map fun p => g p ^ 2).prod := by
  induction l with
  | nil => simp
  | cons p l ih => simp [List.flatMap_cons, ih, pow_two, mul_assoc]

theorem summable_vecCoeff_of_deriv [DecidableEq ι] (F : List (ι × BIdx K) → (ι → 𝔸[K]) → ℂ)
    (hc : ∀ l, Continuous (F l)) (hper : ∀ l, ∀ ξ ∈ vecLattice K ι, ∀ x, F l (ξ + x) = F l x)
    (hfin : ∀ x (z : ι → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        F [] (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) = F [] x)
    (hd : ∀ l p x, HasDerivAt (fun s : ℝ => F l (x + torusPt (Pi.single p s))) (F (p :: l) x) 0) :
    Summable (vecCoeff (F [])) := by
  classical
  choose C hC using fun l => exists_bound_of_periodic (hc l) (hper l)
  set lS : Finset (ι × BIdx K) → List (ι × BIdx K) := fun S => S.toList.flatMap fun p => [p, p]
  set B : ℝ := ∑ S ∈ (Finset.univ : Finset (ι × BIdx K)).powerset, C (lS S)
  have hbound : ∀ ξ : ι → K,
      ‖vecCoeff (F []) ξ‖ * ∏ p, (1 + (2 * π * tau ξ p) ^ 2) ≤ B := by
    intro ξ
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    have h1 := norm_vecCoeff_le (fun x _ => hC (lS S) x) ξ
    rw [vecCoeff_iterDeriv F hc hper hd, norm_mul, prod_map_flatMap_pair, List.norm_prod,
      List.map_map] at h1
    refine le_of_eq_of_le ?_ h1
    rw [mul_comm]
    congr 1
    rw [← Finset.prod_map_toList]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, norm_pow, norm_mul, norm_neg, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos Real.pi_pos, show (2 * π * |tau ξ p|) ^ 2 = 2 ^ 2 * π ^ 2 * |tau ξ p| ^ 2 by ring,
      sq_abs]
    ring
  have hB : 0 ≤ B := le_trans (by positivity) (hbound 0)
  have hdual : Summable (vecCoeff (F []) ∘ dualVec) := by
    refine Summable.of_norm_bounded ((summable_pi_prod summable_inv_one_add_sq
      (fun n => by positivity)).mul_left B) fun n => ?_
    have h := hbound (dualVec n)
    have hpos : 0 < ∏ p, (1 + (2 * π * tau (dualVec n) p) ^ 2) :=
      Finset.prod_pos fun p _ => by positivity
    rw [← le_div_iff₀ hpos] at h
    have hτ : ∀ p, tau (dualVec n) p = n p := fun p => by
      simp only [tau, trace_dualVec_mul, Rat.cast_intCast]
    simp only [hτ] at h
    refine h.trans ?_
    have hpos' : 0 < ∏ p, (1 + (n p : ℝ) ^ 2) := Finset.prod_pos fun p _ => by positivity
    have hle : ∏ p, (1 + (n p : ℝ) ^ 2) ≤ ∏ p, (1 + (2 * π * (n p : ℝ)) ^ 2) :=
      Finset.prod_le_prod (fun p _ => by positivity) fun p _ => by
        have : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
        nlinarith [sq_nonneg (n p : ℝ)]
    refine (div_le_div_of_nonneg_left hB hpos' hle).trans (le_of_eq ?_)
    simp only [div_eq_mul_inv, one_mul]
    rw [Finset.prod_inv_distrib]
  exact (dualVec_injective.summable_iff fun ξ hξ =>
    vecCoeff_eq_zero_of_not_isDual (hper []) hfin fun hd' => hξ (exists_dualVec_eq hd')).1 hdual

end FourierWhittaker

end

end GroundTheory.Automorphic
