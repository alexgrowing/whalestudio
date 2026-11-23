import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.CovTest.SwapLine

def linearSum (a b : ℤ) : MvPolynomial (Fin 2) ℝ := C ((a : ℝ) + b) * X 0 + C 2 * X 1

def quadraticPart (a b : ℤ) : MvPolynomial (Fin 2) ℝ := C ((a : ℝ) * b) * X 0 ^ 2 + C ((a : ℝ) + b) * (X 0 * X 1) + X 1 ^ 2

noncomputable def swapPow (a b : ℤ) : ℕ → Polynomial (MvPolynomial (Fin 2) ℝ)
  | 0 => Polynomial.C (C 2)
  | 1 => Polynomial.C (linearSum a b)
  | n + 2 => Polynomial.C (linearSum a b) * swapPow a b (n + 1) -
      (Polynomial.C (quadraticPart a b) + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * swapPow a b n

def swapR (d : ℕ) (a b : ℤ) (i : ℕ) : MvPolynomial (Fin 2) ℝ := (swapPow a b (d + 2)).coeff i

private theorem hom_cast {σ : Type} {φ : MvPolynomial σ ℝ} {m k : ℕ} (h : φ.IsHomogeneous m) (e : m = k) :
    φ.IsHomogeneous k := e ▸ h

private theorem hom_mul_of {σ : Type} {p f : MvPolynomial σ ℝ} {k m N : ℕ} (hp : p.IsHomogeneous k)
    (hf : f.IsHomogeneous m) (hz : k + m ≠ N → f = 0) : (p * f).IsHomogeneous N := by
  by_cases h : k + m = N
  · exact h ▸ hp.mul hf
  · rw [hz h, mul_zero]; exact isHomogeneous_zero _ _ _

theorem linearSum_isHomogeneous (a b : ℤ) : (linearSum a b).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)

theorem quadraticPart_isHomogeneous (a b : ℤ) : (quadraticPart a b).IsHomogeneous 2 := by
  have h0 := isHomogeneous_X ℝ (0 : Fin 2)
  have h1 := isHomogeneous_X ℝ (1 : Fin 2)
  refine ((hom_cast ((isHomogeneous_C (Fin 2) _).mul (h0.pow 2)) (by omega)).add
    (hom_cast ((isHomogeneous_C (Fin 2) _).mul (h0.mul h1)) (by omega))).add (hom_cast (h1.pow 2) (by omega))

theorem swapPow_coeff_add_two (a b : ℤ) (n i : ℕ) : (swapPow a b (n + 2)).coeff (i + 1) =
    linearSum a b * (swapPow a b (n + 1)).coeff (i + 1) - (quadraticPart a b * (swapPow a b n).coeff (i + 1) +
      C (((a : ℝ) - b) ^ 2) * (swapPow a b n).coeff i) := by
  rw [swapPow, show ∀ T : Polynomial (MvPolynomial (Fin 2) ℝ), (Polynomial.C (quadraticPart a b) +
      Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * T =
      Polynomial.C (quadraticPart a b) * T + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * (Polynomial.X * T) from fun T => by ring]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

theorem swapPow_coeff_zero_add_two (a b : ℤ) (n : ℕ) : (swapPow a b (n + 2)).coeff 0 =
    linearSum a b * (swapPow a b (n + 1)).coeff 0 - quadraticPart a b * (swapPow a b n).coeff 0 := by
  rw [swapPow, show ∀ T : Polynomial (MvPolynomial (Fin 2) ℝ), (Polynomial.C (quadraticPart a b) +
      Polynomial.C (C (((a : ℝ) - b) ^ 2)) * Polynomial.X) * T =
      Polynomial.C (quadraticPart a b) * T + Polynomial.C (C (((a : ℝ) - b) ^ 2)) * (Polynomial.X * T) from fun T => by ring]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero, mul_zero,
    add_zero]

theorem swapPow_coeff (a b : ℤ) (n : ℕ) : ∀ i, ((swapPow a b n).coeff i).IsHomogeneous (n - 2 * i) ∧
    (n < 2 * i → (swapPow a b n).coeff i = 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · intro i
    rcases i with _ | i
    · simp only [swapPow, Polynomial.coeff_C_zero]
      exact ⟨isHomogeneous_C _ _, fun h => absurd h (by omega)⟩
    · simp only [swapPow, Polynomial.coeff_C_succ]
      exact ⟨isHomogeneous_zero _ _ _, by simp⟩
  · intro i
    rcases i with _ | i
    · simp only [swapPow, Polynomial.coeff_C_zero]
      exact ⟨linearSum_isHomogeneous a b, fun h => absurd h (by omega)⟩
    · simp only [swapPow, Polynomial.coeff_C_succ]
      exact ⟨isHomogeneous_zero _ _ _, by simp⟩
  · have h1 := ih (n + 1) (by omega)
    have h0 := ih n (by omega)
    intro i
    rcases i with _ | i
    · rw [swapPow_coeff_zero_add_two]
      refine ⟨(hom_mul_of (linearSum_isHomogeneous a b) (h1 0).1 fun h => absurd h (by omega)).sub
        (hom_mul_of (quadraticPart_isHomogeneous a b) (h0 0).1 fun h => absurd h (by omega)), fun h => absurd h (by omega)⟩
    · rw [swapPow_coeff_add_two]
      refine ⟨(hom_mul_of (linearSum_isHomogeneous a b) (h1 (i + 1)).1 fun h => (h1 (i + 1)).2 (by omega)).sub
        ((hom_mul_of (quadraticPart_isHomogeneous a b) (h0 (i + 1)).1 fun h => (h0 (i + 1)).2 (by omega)).add
          (hom_mul_of (isHomogeneous_C (Fin 2) _) (h0 i).1 fun h => absurd h (by omega))), fun h => ?_⟩
      rw [(h1 (i + 1)).2 (by omega), (h0 (i + 1)).2 (by omega), (h0 i).2 (by omega)]
      simp

theorem swapPow_natDegree_lt (a b : ℤ) (n : ℕ) : (swapPow a b n).natDegree < n + 1 := by
  refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_)
  exact (swapPow_coeff a b n N).2 (by omega)

theorem swapR_isHomogeneous (d : ℕ) (a b : ℤ) (i : ℕ) : (swapR d a b i).IsHomogeneous (d + 2 - 2 * i) :=
  (swapPow_coeff a b (d + 2) i).1

theorem swapR_eq_zero (d : ℕ) (a b : ℤ) {i : ℕ} (h : d + 2 < 2 * i) : swapR d a b i = 0 :=
  (swapPow_coeff a b (d + 2) i).2 h

theorem eval_swapPow {S : Type*} [CommRing S] [Algebra ℝ S] (a b : ℤ) (x : Fin 3 → S) (n : ℕ) :
    Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b n) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ n +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ n := by
  have hs : (aeval ![x 0 + x 1, x 2]).toRingHom (linearSum a b) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) + (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) := by
    simp only [linearSum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, aeval_C, aeval_X, map_ofNat,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have hp : (aeval ![x 0 + x 1, x 2]).toRingHom (quadraticPart a b) +
      (aeval ![x 0 + x 1, x 2]).toRingHom (C (((a : ℝ) - b) ^ 2)) * (x 0 * x 1) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) * (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) := by
    simp only [quadraticPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow, map_sub, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have key : ∀ n, Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b n) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ n +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ n ∧
      Polynomial.eval₂ (aeval ![x 0 + x 1, x 2]).toRingHom (x 0 * x 1) (swapPow a b (n + 1)) =
      (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ (n + 1) +
        (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [swapPow, Polynomial.eval₂_C]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, map_ofNat]
        ring
      · simp only [swapPow, Polynomial.eval₂_C]
        rw [hs]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [swapPow]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_C,
        Polynomial.eval₂_X, ih.1, ih.2]
      rw [hs, hp]
      ring
  exact (key n).1

theorem aeval_swapSum {S : Type*} [CommRing S] [Algebra ℝ S] (d : ℕ) (a b : ℤ) (x : Fin 3 → S) :
    aeval x (swapSum d a b) =
      ∑ i ∈ Finset.range (d + 3), (x 0 * x 1) ^ i * aeval ![x 0 + x 1, x 2] (swapR d a b i) := by
  have h1 := eval_swapPow a b x (d + 2)
  rw [Polynomial.eval₂_eq_sum_range' _ (swapPow_natDegree_lt a b (d + 2))] at h1
  have h2 : aeval x (swapSum d a b) = (algebraMap ℝ S a * x 0 + algebraMap ℝ S b * x 1 + x 2) ^ (d + 2) +
      (algebraMap ℝ S b * x 0 + algebraMap ℝ S a * x 1 + x 2) ^ (d + 2) := by
    simp only [swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul]
  rw [h2, ← h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem swapSum_eq (d : ℕ) (a b : ℤ) : swapSum d a b =
    ∑ i ∈ Finset.range (d + 3), (X 0 * X 1) ^ i * aeval ![X 0 + X 1, X 2] (swapR d a b i) := by
  rw [← aeval_swapSum d a b X, aeval_X_left_apply]

def swapP (d : ℕ) (a b : ℤ) : MvPolynomial (Fin 5) ℝ :=
  ∑ i ∈ Finset.range (d + 3), (∑ k ∈ Finset.range i, (X 3 * X 4) ^ k * (X 0 * (X 3 + X 4 - X 0)) ^ (i - 1 - k)) *
    aeval ![X 3 + X 4, X 2] (swapR d a b i)

theorem onLine_sub_onBase_eq (d : ℕ) (a b : ℤ) :
    onLine d a b - onBase d a b = -((X 4 - X 0) * (X 3 - X 0)) * swapP d a b := by
  have e1 : (X 0 + (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) = X 3 + X 4 := by ring
  have e2 : (X 4 * X 3 : MvPolynomial (Fin 5) ℝ) = X 3 * X 4 := mul_comm _ _
  have e3 : (X 4 + X 3 : MvPolynomial (Fin 5) ℝ) = X 3 + X 4 := add_comm _ _
  rw [onLine, onBase, aeval_swapSum, aeval_swapSum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e1, e2,
    e3]
  rw [swapP, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := geom_sum₂_mul (X 3 * X 4 : MvPolynomial (Fin 5) ℝ) (X 0 * (X 3 + X 4 - X 0)) i
  linear_combination (aeval ![X 3 + X 4, X 2] (swapR d a b i)) * h

private theorem swapR_aeval_isHomogeneous_five_vars (d : ℕ) (a b : ℤ) (i : ℕ) :
    (aeval ![X 3 + X 4, X 2] (swapR d a b i) : MvPolynomial (Fin 5) ℝ).IsHomogeneous (1 * (d + 2 - 2 * i)) :=
  (swapR_isHomogeneous d a b i).aeval _ (Fin.forall_fin_two.2 ⟨(isHomogeneous_X ℝ 3).add (isHomogeneous_X ℝ 4),
    isHomogeneous_X ℝ 2⟩)

theorem swapP_isHomogeneous (d : ℕ) (a b : ℤ) : (swapP d a b).IsHomogeneous d := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  rcases i with _ | i
  · simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
    exact isHomogeneous_zero _ _ _
  · refine hom_mul_of (k := 2 * i) (IsHomogeneous.sum _ _ _ fun k hk => ?_) (swapR_aeval_isHomogeneous_five_vars d a b (i + 1)) fun h => ?_
    · have hk := Finset.mem_range.1 hk
      have h34 := (isHomogeneous_X ℝ (3 : Fin 5)).mul (isHomogeneous_X ℝ (4 : Fin 5))
      have hq := (isHomogeneous_X ℝ (0 : Fin 5)).mul
        (((isHomogeneous_X ℝ (3 : Fin 5)).add (isHomogeneous_X ℝ (4 : Fin 5))).sub (isHomogeneous_X ℝ (0 : Fin 5)))
      exact hom_cast ((h34.pow k).mul (hq.pow (i + 1 - 1 - k))) (by omega)
    · rw [swapR_eq_zero d a b (by omega), map_zero]

theorem eq_of_mul_eq_onLine_sub_onBase (d : ℕ) (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ)
    (h : (X 4 - X 0) * F = onLine d a b - onBase d a b) : F = (X 0 - X 3) * swapP d a b := by
  rw [onLine_sub_onBase_eq] at h
  have hne : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ≠ 0 :=
    sub_ne_zero.2 fun e => absurd (X_injective e) (by decide)
  exact mul_left_cancel₀ hne (by rw [h]; ring)

def fibPoly (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((m.choose j : ℝ) *
    ∫ t in (0 : ℝ)..1, (t * (1 - t)) ^ j * (1 - 4 * (t * (1 - t))) ^ (m - j)) * (X 0 ^ (2 * j) * X 1 ^ (m - j))

theorem aeval_fibPoly (m : ℕ) (a b : ℝ) :
    aeval ![a + b, a * b] (fibPoly m) = ∫ t in (0 : ℝ)..1, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m := by
  have hI : ∀ t : ℝ, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m = ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * (a + b) ^ (2 * j) * (a * b) ^ (m - j) * ((t * (1 - t)) ^ j * (1 - 4 * (t * (1 - t))) ^ (m - j)) := by
    intro t
    rw [show (a * t + b * (1 - t)) * (a * (1 - t) + b * t) =
      t * (1 - t) * (a + b) ^ 2 + (1 - 4 * (t * (1 - t))) * (a * b) by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_pow, ← pow_mul]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finsetSum fun j _ => by apply Continuous.intervalIntegrable; fun_prop]
  simp only [fibPoly, map_sum, map_mul, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem fibPoly_aeval_isHomogeneous (m : ℕ) :
    (aeval ![X 0 + X 1, X 0 * X 1] (fibPoly m) : MvPolynomial (Fin 3) ℝ).IsHomogeneous (2 * m) := by
  simp only [fibPoly, map_sum, map_mul, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, algebraMap_eq]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have h0 := isHomogeneous_X ℝ (0 : Fin 3)
  have h1 := isHomogeneous_X ℝ (1 : Fin 3)
  exact hom_cast (((isHomogeneous_C _ _).mul (isHomogeneous_C _ _)).mul
    (((h0.add h1).pow (2 * j)).mul ((h0.mul h1).pow (m - j)))) (by omega)

def swapG : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ
  | 0, _, _ => 0
  | d + 1, a, b => C (1 / 2 : ℝ) * X 0 * ∑ i ∈ Finset.range (d + 3), ∑ k ∈ Finset.range i,
      (X 0 * X 1) ^ k * aeval ![X 0 + X 1, X 0 * X 1] (fibPoly (i - 1 - k)) * aeval ![X 0 + X 1, X 2] (swapR d a b i)

theorem swapG_homog : Homog swapG := by
  intro D a b
  rcases D with _ | d
  · exact isHomogeneous_zero _ _ _
  · have h0 := isHomogeneous_X ℝ (0 : Fin 3)
    have h1 := isHomogeneous_X ℝ (1 : Fin 3)
    refine hom_cast (((isHomogeneous_C _ _).mul h0).mul (IsHomogeneous.sum _ _ d fun i _ =>
      IsHomogeneous.sum _ _ d fun k hk => ?_)) (by omega)
    have hk := Finset.mem_range.1 hk
    have hR : (aeval ![X 0 + X 1, X 2] (swapR d a b i) : MvPolynomial (Fin 3) ℝ).IsHomogeneous (1 * (d + 2 - 2 * i)) :=
      (swapR_isHomogeneous d a b i).aeval _ (Fin.forall_fin_two.2 ⟨h0.add h1, isHomogeneous_X ℝ 2⟩)
    refine hom_mul_of (((h0.mul h1).pow k).mul (fibPoly_aeval_isHomogeneous (i - 1 - k))) hR fun h => ?_
    rw [swapR_eq_zero d a b (by omega), map_zero]

section Universal

open GlobalTheory.LineForm

private theorem aeval_aeval_two {σ S : Type} [CommRing S] [Algebra ℝ S] (f : σ → S) (u v : MvPolynomial σ ℝ)
    (p : MvPolynomial (Fin 2) ℝ) : aeval f (aeval ![u, v] p) = aeval ![aeval f u, aeval f v] p := by
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem sum_idx {M : Type} [AddCommMonoid M] (d : ℕ) (f : ℕ × ℕ → M) :
    ∑ x ∈ idx d, f x = ∑ i ∈ Finset.range (d + 3), ∑ k ∈ Finset.range i, f (i, k) := by
  rw [idx, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.1 hi
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem sum_monomial_coeffs_swap (d : ℕ) (a b : ℤ) : upperParabolic (idx d) expo (coefW (swapR d a b)) = swapP d a b := by
  rw [upperParabolic, sum_idx, swapP]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [coefW, expo, map_mul, map_pow, aeval_aeval_two, map_add, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dvd_downP_sub_baseT (d : ℕ) (R : ℕ → MvPolynomial (Fin 2) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      downP (idx d) expo (coefW R) - aeval ![X 1 + X 2, X 3, X 0] (baseT d R) := by
  rw [downP, baseT, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun x _ => ?_
  simp only [coefW, map_mul, map_pow, aeval_aeval_two, map_add, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (X 3 : MvPolynomial (Fin 4) ℝ) (X 1 * X 2) x.2
  refine ⟨-(c * aeval ![X 1 + X 2, X 3] (pm (expo x)) * aeval ![X 1 + X 2, X 0] (R x.1)), ?_⟩
  linear_combination (-(aeval ![X 1 + X 2, X 3] (pm (expo x)) * aeval ![X 1 + X 2, X 0] (R x.1))) * hc

theorem pm_aeval_isHomogeneous (m : ℕ) :
    (aeval ![X 0 + X 1, X 0 * X 1] (pm m) : MvPolynomial (Fin 3) ℝ).IsHomogeneous (2 * m) := by
  rw [pm, map_sum]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have h0 := isHomogeneous_X ℝ (0 : Fin 3)
  have h1 := isHomogeneous_X ℝ (1 : Fin 3)
  have h4 : (4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 0 := by
    have := isHomogeneous_C (Fin 3) (4 : ℝ)
    rwa [map_ofNat] at this
  rw [map_mul, map_mul, aeval_C, algebraMap_eq]
  simp only [map_mul, map_pow, map_sub, map_ofNat, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have hq : ((X 0 + X 1) ^ 2 - 4 * (X 0 * X 1) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
    (hom_cast ((h0.add h1).pow 2) (by omega)).sub (hom_cast (h4.mul (h0.mul h1)) (by omega))
  exact hom_cast (((isHomogeneous_C _ _).mul ((h0.mul h1).pow (m - j))).mul (hq.pow j)) (by omega)

theorem baseT_aeval_isHomogeneous (d : ℕ) (a b : ℤ) :
    (aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (swapR d a b)) : MvPolynomial (Fin 3) ℝ).IsHomogeneous d := by
  have h0 := isHomogeneous_X ℝ (0 : Fin 3)
  have h1 := isHomogeneous_X ℝ (1 : Fin 3)
  rw [baseT, map_sum]
  refine IsHomogeneous.sum _ _ _ fun x hx => ?_
  have hk : x.2 < x.1 := (Finset.mem_filter.1 hx).2
  simp only [map_mul, map_pow, aeval_aeval_two, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hR : (aeval ![X 0 + X 1, X 2] (swapR d a b x.1) : MvPolynomial (Fin 3) ℝ).IsHomogeneous
      (1 * (d + 2 - 2 * x.1)) :=
    (swapR_isHomogeneous d a b x.1).aeval _ (Fin.forall_fin_two.2 ⟨h0.add h1, isHomogeneous_X ℝ 2⟩)
  refine hom_mul_of (((h0.mul h1).pow x.2).mul (pm_aeval_isHomogeneous (expo x))) hR fun h => ?_
  rw [expo] at h
  rw [swapR_eq_zero d a b (by omega), map_zero]

theorem exists_swap_coefficients : ∃ R : ℕ → ℤ → ℤ → ℕ → MvPolynomial (Fin 2) ℝ, ∀ (d : ℕ) (a b : ℤ),
    (∀ F : MvPolynomial (Fin 5) ℝ, (X 4 - X 0) * F = onLine d a b - onBase d a b →
      F = (X 0 - X 3) * upperParabolic (idx d) expo (coefW (R d a b))) ∧
    (upperParabolic (idx d) expo (coefW (R d a b))).IsHomogeneous d ∧
    ((X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      downP (idx d) expo (coefW (R d a b)) - aeval ![X 1 + X 2, X 3, X 0] (baseT d (R d a b))) ∧
    (C (1 / 2 : ℝ) * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] (baseT d (R d a b)) :
      MvPolynomial (Fin 3) ℝ).IsHomogeneous (d + 1) := by
  refine ⟨swapR, fun d a b => ⟨fun F hF => ?_, ?_, dvd_downP_sub_baseT d _, ?_⟩⟩
  · rw [sum_monomial_coeffs_swap]; exact eq_of_mul_eq_onLine_sub_onBase d a b F hF
  · rw [sum_monomial_coeffs_swap]; exact swapP_isHomogeneous d a b
  · exact hom_cast (((isHomogeneous_C _ _).mul (isHomogeneous_X ℝ (0 : Fin 3))).mul
      (baseT_aeval_isHomogeneous d a b)) (by omega)

end Universal

end GlobalTheory.CovTest.SwapLine

end
