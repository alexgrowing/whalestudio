import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SqrtSumPdTMulSubLe

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory Finset
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem powMul_bound_le {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) {p q i : ℕ} (hp : 1 ≤ p)
    (hq : q + 1 ≤ p) (hqi : q + i ≤ p) :
    (p : ℝ) ^ i * (B * L ^ q * (q : ℝ) ^ q) ≤ B * L ^ (p - 1) * (p : ℝ) ^ p := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (q : ℝ) ^ q ≤ (p : ℝ) ^ q :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : q ≤ p)) _
  have h2 : (p : ℝ) ^ i * (p : ℝ) ^ q ≤ (p : ℝ) ^ p := by
    rw [← pow_add]; exact pow_le_pow_right₀ hp' (by omega)
  have h3 : L ^ q ≤ L ^ (p - 1) := pow_le_pow_right₀ hL (by omega)
  have hpi : 0 ≤ (p : ℝ) ^ i := by positivity
  have hqq : 0 ≤ (q : ℝ) ^ q := by positivity
  calc (p : ℝ) ^ i * (B * L ^ q * (q : ℝ) ^ q) = B * L ^ q * ((p : ℝ) ^ i * (q : ℝ) ^ q) := by ring
    _ ≤ B * L ^ (p - 1) * ((p : ℝ) ^ i * (p : ℝ) ^ q) := by gcongr
    _ ≤ B * L ^ (p - 1) * (p : ℝ) ^ p := by gcongr

theorem coefTerm_le {B L Ma : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hMa : 0 ≤ Ma) {p k i q : ℕ}
    (hp : 1 ≤ p) (hk : k ≤ p) (hqi : q + i ≤ p) :
    (k.choose i : ℝ) * (Ma ^ i * i.factorial) * (B * L ^ q * (q : ℝ) ^ q) ≤
      B * L ^ p * (p : ℝ) ^ p * (Ma / L) ^ i := by
  have hL0 : 0 < L := by linarith
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hc : (k.choose i : ℝ) * i.factorial ≤ (p : ℝ) ^ i := by
    have : k.choose i * i.factorial ≤ p ^ i := by
      calc k.choose i * i.factorial = k.descFactorial i := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
        _ ≤ k ^ i := Nat.descFactorial_le_pow _ _
        _ ≤ p ^ i := Nat.pow_le_pow_left hk _
    exact_mod_cast this
  have hiq : i ≤ p := by omega
  have h1 : (q : ℝ) ^ q ≤ (p : ℝ) ^ q :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : q ≤ p)) _
  have h2 : (p : ℝ) ^ i * (p : ℝ) ^ q ≤ (p : ℝ) ^ p := by
    rw [← pow_add]; exact pow_le_pow_right₀ hp' (by omega)
  have h3 : L ^ q ≤ L ^ (p - i) := pow_le_pow_right₀ hL (by omega)
  have hLp : L ^ p = L ^ (p - i) * L ^ i := by rw [← pow_add, Nat.sub_add_cancel hiq]
  have hLi : 0 < L ^ i := by positivity
  rw [div_pow, hLp]
  have hqq : 0 ≤ (q : ℝ) ^ q := by positivity
  have hMi : 0 ≤ Ma ^ i := by positivity
  have hfac : 0 ≤ (i.factorial : ℝ) := by positivity
  have hch : 0 ≤ (k.choose i : ℝ) := by positivity
  calc (k.choose i : ℝ) * (Ma ^ i * i.factorial) * (B * L ^ q * (q : ℝ) ^ q)
      = Ma ^ i * B * L ^ q * (((k.choose i : ℝ) * i.factorial) * (q : ℝ) ^ q) := by ring
    _ ≤ Ma ^ i * B * L ^ (p - i) * ((p : ℝ) ^ i * (p : ℝ) ^ q) := by gcongr
    _ ≤ Ma ^ i * B * L ^ (p - i) * (p : ℝ) ^ p := by gcongr
    _ = B * (L ^ (p - i) * L ^ i) * (p : ℝ) ^ p * (Ma ^ i / L ^ i) := by
        field_simp

theorem sum_filter_antidiagonal_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (k : ℕ) :
    ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1), r ^ ij.1 ≤ 2 * r := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [lt_self_iff_false, if_false, add_zero, Nat.succ_pos, if_true]
  have h1r : 0 < 1 - r := by linarith
  have hg : ∑ i ∈ range k, r ^ i ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ h1r, geom_sum_mul_neg]
    linarith [pow_nonneg hr0 k]
  calc ∑ i ∈ range k, r ^ (i + 1) = r * ∑ i ∈ range k, r ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ r * (1 / (1 - r)) := by gcongr
    _ ≤ 2 * r := by
        rw [mul_one_div, div_le_iff₀ h1r]; nlinarith

theorem contDiff_weight {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (s : ℕ) :
    ContDiff ℝ ∞ (fun y ↦ ((χ y : ℂ)) ^ s) :=
  (Complex.ofRealCLM.contDiff.comp hχ).pow s

theorem norm_cutoff_pow {χ : EuclideanSpace ℝ (Fin n) → ℝ} (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (s : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖((χ x : ℂ)) ^ s‖ = χ x ^ s := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (h01 x).1]

theorem sqrt_sum_const_mul_hsD_pdT {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u) {c : ℝ}
    (hc : 0 ≤ c) (j k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ I : Fin k → Fin n, (c * hsD j (pdT I u) x) ^ 2) = c * hsD (j + k) u x := by
  rw [sqrt_sum_sq_const_mul, abs_of_nonneg hc, ← hsD_add_sq hu, Real.sqrt_sq (hsD_nonneg _ _ _)]

theorem sqrt_sum_hsD_weight_le {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {k s j : ℕ} (hjL : j ≤ L₀) (hjs : j + k ≤ s) (x : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ I : Fin k → Fin n, hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2) ≤
      ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
        (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x) := by
  have hw := contDiff_weight hχ s
  have hχ0 := (h01 x).1
  set c : ℕ × ℕ → ℝ := fun ij ↦ (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * χ x ^ (s - ij.1)
    with hc
  have hc0 : ∀ ij, 0 ≤ c ij := fun ij ↦ by simp only [hc]; positivity
  have hI : ∀ I : Fin k → Fin n, hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ≤
      ∑ ij ∈ antidiagonal j, c ij * hsD ij.2 (pdT I u) x := by
    intro I
    refine (hsD_mul_le j hw (contDiff_pdT hu I) x).trans (Finset.sum_le_sum fun ij hij ↦ ?_)
    have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
    have hb := hK s ij.1 x (by omega) (by omega)
    have := hsD_nonneg ij.2 (pdT I u) x
    calc (j.choose ij.1 : ℝ) * hsD ij.1 (fun y ↦ ((χ y : ℂ)) ^ s) x * hsD ij.2 (pdT I u) x
        ≤ (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1 * χ x ^ (s - ij.1)) *
            hsD ij.2 (pdT I u) x := by gcongr
      _ = c ij * hsD ij.2 (pdT I u) x := by simp only [hc]; ring
  calc Real.sqrt (∑ I : Fin k → Fin n, hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2)
      ≤ Real.sqrt (∑ I : Fin k → Fin n,
          (∑ ij ∈ antidiagonal j, c ij * hsD ij.2 (pdT I u) x) ^ 2) :=
        sqrt_sum_sq_mono fun I ↦ ⟨hsD_nonneg _ _ _, hI I⟩
    _ ≤ ∑ ij ∈ antidiagonal j,
          Real.sqrt (∑ I : Fin k → Fin n, (c ij * hsD ij.2 (pdT I u) x) ^ 2) :=
        sqrt_sum_sq_sum_le _ _
    _ = ∑ ij ∈ antidiagonal j, c ij * hsD (ij.2 + k) u x :=
        Finset.sum_congr rfl fun ij _ ↦ sqrt_sum_const_mul_hsD_pdT hu (hc0 ij) _ _ x
    _ ≤ _ := by
        refine Finset.sum_le_sum fun ij hij ↦ ?_
        have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
        have hpow : χ x ^ (s - ij.1) ≤ χ x ^ (ij.2 + k) :=
          pow_le_pow_of_le_one hχ0 (h01 x).2 (by omega)
        have := hsD_nonneg (ij.2 + k) u x
        calc c ij * hsD (ij.2 + k) u x
            = (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * (χ x ^ (s - ij.1) * hsD (ij.2 + k) u x) := by
              simp only [hc]; ring
          _ ≤ _ := by gcongr

theorem weight_hsD_add_le {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {k s m : ℕ} (hmL : m ≤ L₀) (hms : m + k ≤ s) (x : EuclideanSpace ℝ (Fin n)) :
    χ x ^ s * hsD (m + k) u x ≤
      Real.sqrt (∑ I : Fin k → Fin n, hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2) +
      ∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1), (m.choose ij.1 : ℝ) *
        (K * (s : ℝ) ^ ij.1) * (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x) := by
  have hw := contDiff_weight hχ s
  have hχ0 := (h01 x).1
  set c : ℕ × ℕ → ℝ := fun ij ↦ (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * χ x ^ (s - ij.1)
    with hc
  have hc0 : ∀ ij, 0 ≤ c ij := fun ij ↦ by simp only [hc]; positivity
  set F := (antidiagonal m).filter (fun ij ↦ 0 < ij.1) with hF
  have hI : ∀ I : Fin k → Fin n, χ x ^ s * hsD m (pdT I u) x ≤
      hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x +
        ∑ ij ∈ F, c ij * hsD ij.2 (pdT I u) x := by
    intro I
    have h := norm_mul_hsD_le hw (contDiff_pdT hu I) (k := m) (x := x)
    rw [norm_cutoff_pow h01] at h
    refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun ij hij ↦ ?_))
    have h1 : ij.1 + ij.2 = m := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
    have hb := hK s ij.1 x (by omega) (by omega)
    have := hsD_nonneg ij.2 (pdT I u) x
    calc (m.choose ij.1 : ℝ) * hsD ij.1 (fun y ↦ ((χ y : ℂ)) ^ s) x * hsD ij.2 (pdT I u) x
        ≤ (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1 * χ x ^ (s - ij.1)) *
            hsD ij.2 (pdT I u) x := by gcongr
      _ = c ij * hsD ij.2 (pdT I u) x := by simp only [hc]; ring
  have hL : χ x ^ s * hsD (m + k) u x =
      Real.sqrt (∑ I : Fin k → Fin n, (χ x ^ s * hsD m (pdT I u) x) ^ 2) := by
    rw [sqrt_sum_const_mul_hsD_pdT hu (by positivity)]
  rw [hL]
  calc Real.sqrt (∑ I : Fin k → Fin n, (χ x ^ s * hsD m (pdT I u) x) ^ 2)
      ≤ Real.sqrt (∑ I : Fin k → Fin n, (hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x +
          ∑ ij ∈ F, c ij * hsD ij.2 (pdT I u) x) ^ 2) :=
        sqrt_sum_sq_mono fun I ↦ ⟨by have := hsD_nonneg m (pdT I u) x; positivity, hI I⟩
    _ ≤ Real.sqrt (∑ I : Fin k → Fin n, hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2) +
          Real.sqrt (∑ I : Fin k → Fin n, (∑ ij ∈ F, c ij * hsD ij.2 (pdT I u) x) ^ 2) :=
        sqrt_sum_sq_add_le _ _
    _ ≤ Real.sqrt (∑ I : Fin k → Fin n, hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2) +
          ∑ ij ∈ F, Real.sqrt (∑ I : Fin k → Fin n, (c ij * hsD ij.2 (pdT I u) x) ^ 2) := by
        gcongr
        exact sqrt_sum_sq_sum_le _ _
    _ = Real.sqrt (∑ I : Fin k → Fin n, hsD m (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2) +
          ∑ ij ∈ F, c ij * hsD (ij.2 + k) u x := by
        congr 1
        exact Finset.sum_congr rfl fun ij _ ↦ sqrt_sum_const_mul_hsD_pdT hu (hc0 ij) _ _ x
    _ ≤ _ := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun ij hij ↦ ?_)
        have h1 : ij.1 + ij.2 = m := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have hpow : χ x ^ (s - ij.1) ≤ χ x ^ (ij.2 + k) :=
          pow_le_pow_of_le_one hχ0 (h01 x).2 (by omega)
        have := hsD_nonneg (ij.2 + k) u x
        calc c ij * hsD (ij.2 + k) u x
            = (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * (χ x ^ (s - ij.1) * hsD (ij.2 + k) u x) := by
              simp only [hc]; ring
          _ ≤ _ := by gcongr

theorem diffOp_pdT_eq {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (ha : ∀ α ∈ A, ContDiff ℝ ∞ (a α)) {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hPu : ∀ x ∈ U, diffOp A a u x = 0)
    {k : ℕ} (I : Fin k → Fin n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    diffOp A a (pdT I u) x = ∑ α ∈ A, (a α x * pdT I (pderiv α u) x -
      pdT I (fun y ↦ a α y * pderiv α u y) x) := by
  have h0 : pdT I (diffOp A a u) x = 0 := by
    have hev : diffOp A a u =ᶠ[nhds x] fun _ ↦ (0 : ℂ) := by
      filter_upwards [hU.mem_nhds hx] with y hy using hPu y hy
    rw [pdT, dT_congr_of_eventuallyEq hev]
    simp [dT]
  have hsum : pdT I (diffOp A a u) x = ∑ α ∈ A, pdT I (fun y ↦ a α y * pderiv α u y) x := by
    have e : diffOp A a u = fun y ↦ ∑ α ∈ A, a α y * pderiv α u y := rfl
    rw [e, pdT, dT_sum A _ (fun α hα ↦ (ha α hα).mul (contDiff_pderiv hu α))]
    rfl
  have hD : diffOp A a (pdT I u) x = ∑ α ∈ A, a α x * pdT I (pderiv α u) x := by
    simp only [diffOp]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [pdT_pderiv_comm hu I α]
  rw [hD, Finset.sum_sub_distrib, ← hsum, h0, sub_zero]

theorem sqrt_sum_diffOp_pdT_le {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (ha : ∀ α ∈ A, ContDiff ℝ ∞ (a α))
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hPu : ∀ x ∈ U, diffOp A a u x = 0)
    {Ca Ma : ℝ} (hCa : 0 ≤ Ca) (hMa : 0 ≤ Ma)
    (hcoef : ∀ α ∈ A, ∀ x ∈ U, ∀ i, hsD i (a α) x ≤ Ca * Ma ^ i * i.factorial)
    (k : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (pdT I u) x‖ ^ 2) ≤
      ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * hsD (mabs α + ij.2) u x := by
  calc Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (pdT I u) x‖ ^ 2)
      ≤ Real.sqrt (∑ I : Fin k → Fin n, (∑ α ∈ A,
          ‖pdT I (fun y ↦ a α y * pderiv α u y) x - a α x * pdT I (pderiv α u) x‖) ^ 2) := by
        refine sqrt_sum_sq_mono fun I ↦ ⟨norm_nonneg _, ?_⟩
        rw [diffOp_pdT_eq ha hu hU hPu I hx]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
        rw [norm_sub_rev]
    _ ≤ ∑ α ∈ A, Real.sqrt (∑ I : Fin k → Fin n,
          ‖pdT I (fun y ↦ a α y * pderiv α u y) x - a α x * pdT I (pderiv α u) x‖ ^ 2) :=
        sqrt_sum_sq_sum_le _ _
    _ ≤ ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
          (k.choose ij.1 : ℝ) * hsD ij.1 (a α) x * hsD ij.2 (pderiv α u) x := by
        refine Finset.sum_le_sum fun α hα ↦ ?_
        exact sqrt_sum_pdT_mul_sub_le (ha α hα) (contDiff_pderiv hu α) k x
    _ ≤ _ := by
        refine Finset.sum_le_sum fun α hα ↦ Finset.sum_le_sum fun ij _ ↦ ?_
        have h1 := hcoef α hα x hx ij.1
        have h2 := hsD_pderiv_le hu α ij.2 x
        have := hsD_nonneg ij.2 (pderiv α u) x
        have := hsD_nonneg ij.1 (a α) x
        calc (k.choose ij.1 : ℝ) * hsD ij.1 (a α) x * hsD ij.2 (pderiv α u) x
            ≤ (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
                hsD (mabs α + ij.2) u x := by gcongr

theorem sqrt_sum_diffOp_weight_le {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (ha : ∀ α ∈ A, ContDiff ℝ ∞ (a α))
    {A₀ : ℝ} (hA₀0 : 0 ≤ A₀) (hA₀ : ∀ α ∈ A, ∀ x, ‖a α x‖ ≤ A₀) {m : ℕ}
    (hA : ∀ α ∈ A, mabs α ≤ m)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hPu : ∀ x ∈ U, diffOp A a u x = 0)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχU : ∀ x, x ∉ U → χ x = 0)
    {Ca Ma : ℝ} (hCa : 0 ≤ Ca) (hMa : 0 ≤ Ma)
    (hcoef : ∀ α ∈ A, ∀ x ∈ U, ∀ i, hsD i (a α) x ≤ Ca * Ma ^ i * i.factorial)
    {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    (hmL : m ≤ L₀) {k s : ℕ} (hs : s = k + m) (hs1 : 1 ≤ s) (x : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ I : Fin k → Fin n,
        ‖diffOp A a (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x‖ ^ 2) ≤
      ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
          (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
            (χ x ^ (mabs α + ij.2) * hsD (mabs α + ij.2) u x) +
        ∑ α ∈ A, A₀ * ∑ ij ∈ (antidiagonal (mabs α)).filter (fun ij ↦ 0 < ij.1),
          ((mabs α).choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
            (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x) := by
  have hw := contDiff_weight hχ s
  have hχ0 := (h01 x).1
  have hdec : ∀ I : Fin k → Fin n, diffOp A a (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x =
      ((χ x : ℂ)) ^ s * diffOp A a (pdT I u) x + ∑ α ∈ A, a α x *
        (pderiv α (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x -
          ((χ x : ℂ)) ^ s * pderiv α (pdT I u) x) := by
    intro I
    simp only [diffOp]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun α _ ↦ by ring
  set c : ℕ → ℕ × ℕ → ℝ := fun q ij ↦ (q.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
    χ x ^ (s - ij.1) with hc
  have hc0 : ∀ q ij, 0 ≤ c q ij := fun q ij ↦ by simp only [hc]; positivity
  set F : ℕ → Finset (ℕ × ℕ) := fun q ↦ (antidiagonal q).filter (fun ij ↦ 0 < ij.1) with hF
  have hcomm : ∀ (I : Fin k → Fin n), ∀ α ∈ A,
      ‖pderiv α (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x -
        ((χ x : ℂ)) ^ s * pderiv α (pdT I u) x‖ ≤
      ∑ ij ∈ F (mabs α), c (mabs α) ij * hsD ij.2 (pdT I u) x := by
    intro I α hα
    refine (norm_pderiv_mul_sub_le hw (contDiff_pdT hu I) α x).trans
      (Finset.sum_le_sum fun ij hij ↦ ?_)
    have h1 : ij.1 + ij.2 = mabs α := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
    have hαm := hA α hα
    have hb := hK s ij.1 x (by omega) (by omega)
    have := hsD_nonneg ij.2 (pdT I u) x
    calc ((mabs α).choose ij.1 : ℝ) * hsD ij.1 (fun y ↦ ((χ y : ℂ)) ^ s) x *
          hsD ij.2 (pdT I u) x
        ≤ ((mabs α).choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1 * χ x ^ (s - ij.1)) *
            hsD ij.2 (pdT I u) x := by gcongr
      _ = c (mabs α) ij * hsD ij.2 (pdT I u) x := by simp only [hc]; ring
  have hI : ∀ I : Fin k → Fin n,
      ‖diffOp A a (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x‖ ≤
        χ x ^ s * ‖diffOp A a (pdT I u) x‖ +
          ∑ α ∈ A, A₀ * ∑ ij ∈ F (mabs α), c (mabs α) ij * hsD ij.2 (pdT I u) x := by
    intro I
    rw [hdec I]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_cutoff_pow h01]
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα ↦ ?_)
      rw [norm_mul]
      exact mul_le_mul (hA₀ α hα x) (hcomm I α hα) (norm_nonneg _) hA₀0
  have hsplit : Real.sqrt (∑ I : Fin k → Fin n,
        ‖diffOp A a (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x‖ ^ 2) ≤
      χ x ^ s * Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (pdT I u) x‖ ^ 2) +
        ∑ α ∈ A, A₀ * ∑ ij ∈ F (mabs α), c (mabs α) ij * hsD (ij.2 + k) u x := by
    calc Real.sqrt (∑ I : Fin k → Fin n,
          ‖diffOp A a (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x‖ ^ 2)
        ≤ Real.sqrt (∑ I : Fin k → Fin n, (χ x ^ s * ‖diffOp A a (pdT I u) x‖ +
            ∑ α ∈ A, A₀ * ∑ ij ∈ F (mabs α), c (mabs α) ij * hsD ij.2 (pdT I u) x) ^ 2) :=
          sqrt_sum_sq_mono fun I ↦ ⟨norm_nonneg _, hI I⟩
      _ ≤ Real.sqrt (∑ I : Fin k → Fin n, (χ x ^ s * ‖diffOp A a (pdT I u) x‖) ^ 2) +
            Real.sqrt (∑ I : Fin k → Fin n, (∑ α ∈ A, A₀ * ∑ ij ∈ F (mabs α),
              c (mabs α) ij * hsD ij.2 (pdT I u) x) ^ 2) := sqrt_sum_sq_add_le _ _
      _ ≤ χ x ^ s * Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (pdT I u) x‖ ^ 2) +
            ∑ α ∈ A, A₀ * ∑ ij ∈ F (mabs α), c (mabs α) ij * hsD (ij.2 + k) u x := by
          refine add_le_add (le_of_eq ?_) ?_
          · rw [sqrt_sum_sq_const_mul, abs_of_nonneg (by positivity)]
          · refine (sqrt_sum_sq_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
            rw [sqrt_sum_sq_const_mul, abs_of_nonneg hA₀0]
            gcongr
            refine (sqrt_sum_sq_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun ij _ ↦ sqrt_sum_const_mul_hsD_pdT hu (hc0 _ ij) _ _ x
  refine hsplit.trans (add_le_add ?_ ?_)
  · by_cases hx : x ∈ U
    · have h := sqrt_sum_diffOp_pdT_le ha hu hU hPu hCa hMa hcoef k hx
      calc χ x ^ s * Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (pdT I u) x‖ ^ 2)
          ≤ χ x ^ s * ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
              (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
                hsD (mabs α + ij.2) u x := by gcongr
        _ = ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
              (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
                (χ x ^ s * hsD (mabs α + ij.2) u x) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun α _ ↦ ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun ij _ ↦ by ring
        _ ≤ _ := by
            refine Finset.sum_le_sum fun α hα ↦ Finset.sum_le_sum fun ij hij ↦ ?_
            have h1 : ij.1 + ij.2 = k := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
            have hαm := hA α hα
            have hpow : χ x ^ s ≤ χ x ^ (mabs α + ij.2) :=
              pow_le_pow_of_le_one hχ0 (h01 x).2 (by omega)
            have := hsD_nonneg (mabs α + ij.2) u x
            gcongr
    · have h0 : χ x = 0 := hχU x hx
      rw [h0, zero_pow (by omega), zero_mul]
      refine Finset.sum_nonneg fun α _ ↦ Finset.sum_nonneg fun ij _ ↦ ?_
      have := hsD_nonneg (mabs α + ij.2) u x
      positivity
  · refine Finset.sum_le_sum fun α hα ↦
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij hij ↦ ?_) hA₀0
    have h1 : ij.1 + ij.2 = mabs α := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
    have hαm := hA α hα
    have hpow : χ x ^ (s - ij.1) ≤ χ x ^ (ij.2 + k) :=
      pow_le_pow_of_le_one hχ0 (h01 x).2 (by omega)
    have := hsD_nonneg (ij.2 + k) u x
    calc c (mabs α) ij * hsD (ij.2 + k) u x
        = ((mabs α).choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
            (χ x ^ (s - ij.1) * hsD (ij.2 + k) u x) := by simp only [hc]; ring
      _ ≤ _ := by gcongr

theorem hsD_eq_zero_of_eventuallyEq_zero {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {x : EuclideanSpace ℝ (Fin n)} (h : f =ᶠ[nhds x] fun _ ↦ 0) (k : ℕ) : hsD k f x = 0 := by
  rw [hsD_congr_of_eventuallyEq h]
  simp [hsD, pdT, dT, iteratedFDeriv_fun_zero]

theorem dT_eventuallyEq_zero_of_not_mem_tsupport {f : EuclideanSpace ℝ (Fin n) → ℂ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport f) {k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) : dT v f =ᶠ[nhds x] fun _ ↦ 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [dT_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hy)]
  simp [dT]

def wN (χ : EuclideanSpace ℝ (Fin n) → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) (q : ℕ) : ℝ :=
  l2n (fun x ↦ χ x ^ q * hsD q u x)

theorem wN_nonneg (χ : EuclideanSpace ℝ (Fin n) → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) (q : ℕ) :
    0 ≤ wN χ u q :=
  l2Norm_nonneg_alt _

theorem l2Norm_sum_const_mul_le {ι : Type*} (T : Finset ι) (c : ι → ℝ) (hc : ∀ t ∈ T, 0 ≤ c t)
    (G : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hG : ∀ t ∈ T, MemLp (G t) 2 volume) :
    l2n (fun x ↦ ∑ t ∈ T, c t * G t x) ≤ ∑ t ∈ T, c t * l2n (G t) := by
  refine (l2Norm_finset_sum_le T (fun t x ↦ c t * G t x) fun t ht ↦ (hG t ht).const_mul _).trans
    (Finset.sum_le_sum fun t ht ↦ ?_)
  rw [l2Norm_const_mul, abs_of_nonneg (hc t ht)]

theorem memLp_sum_mul {ι : Type*} (T : Finset ι) (c : ι → ℝ)
    (G : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hG : ∀ t ∈ T, MemLp (G t) 2 volume) :
    MemLp (fun x ↦ ∑ t ∈ T, c t * G t x) 2 volume :=
  memLp_finsetSum T fun t ht ↦ (hG t ht).const_mul _

theorem wN_step {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (ha : ∀ α ∈ A, ContDiff ℝ ∞ (a α))
    {A₀ : ℝ} (hA₀0 : 0 ≤ A₀) (hA₀ : ∀ α ∈ A, ∀ x, ‖a α x‖ ≤ A₀) (hA : ∀ α ∈ A, mabs α ≤ m)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u) (hu_c : HasCompactSupport u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hPu : ∀ x ∈ U, diffOp A a u x = 0)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχU : tsupport χ ⊆ U)
    {Ca Ma : ℝ} (hCa : 0 ≤ Ca) (hMa : 0 ≤ Ma)
    (hcoef : ∀ α ∈ A, ∀ x ∈ U, ∀ i, hsD i (a α) x ≤ Ca * Ma ^ i * i.factorial)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hE : ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ U → l2n (hsD m v) ≤
        C₀ * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ range m, l2n (hsD j v)))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    (k : ℕ) :
    wN χ u (m + k) ≤
      C₀ * ((∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
            (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * wN χ u (mabs α + ij.2)) +
          (∑ α ∈ A, A₀ * ∑ ij ∈ (antidiagonal (mabs α)).filter (fun ij ↦ 0 < ij.1),
            ((mabs α).choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) +
          ∑ j ∈ range m, ∑ ij ∈ antidiagonal j,
            (j.choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) +
      ∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1),
        (m.choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k) := by
  classical
  set s := m + k with hs
  have hs1 : 1 ≤ s := by omega
  have hχU' : ∀ x, x ∉ U → χ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)
  set v : (Fin k → Fin n) → EuclideanSpace ℝ (Fin n) → ℂ :=
    fun I y ↦ ((χ y : ℂ)) ^ s * pdT I u y with hv
  have hvC : ∀ I, ContDiff ℝ ∞ (v I) := fun I ↦ (contDiff_weight hχ s).mul (contDiff_pdT hu I)
  have hvz : ∀ I x, x ∉ tsupport u → v I =ᶠ[nhds x] fun _ ↦ 0 := by
    intro I x hx
    filter_upwards [dT_eventuallyEq_zero_of_not_mem_tsupport hx (fun l ↦ ev (I l))] with y hy
    simp only [hv, pdT]
    rw [hy, mul_zero]
  have hvcs : ∀ I, HasCompactSupport (v I) := fun I ↦
    HasCompactSupport.intro hu_c fun x hx ↦ (hvz I x hx).self_of_nhds
  have hvU : ∀ I, tsupport (v I) ⊆ U := by
    intro I
    refine (tsupport_mul_subset_left).trans ((closure_mono ?_).trans hχU)
    intro y hy h
    apply hy
    simp only [h, Complex.ofReal_zero, zero_pow (by omega : s ≠ 0)]
  have mem : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous f →
      (∀ x, x ∉ tsupport u → f x = 0) → MemLp f 2 volume := fun hc hz ↦
    memLp_two_of_continuous_hasCompactSupport hc (HasCompactSupport.intro hu_c hz)
  have hzu : ∀ x, x ∉ tsupport u → u =ᶠ[nhds x] fun _ ↦ 0 := fun x hx ↦
    notMem_tsupport_iff_eventuallyEq.1 hx
  have memg : ∀ q, MemLp (fun x ↦ χ x ^ q * hsD q u x) 2 volume := fun q ↦
    mem ((hχ.continuous.pow q).mul (continuous_hsD hu q)) fun x hx ↦ by
      rw [hsD_eq_zero_of_eventuallyEq_zero (hzu x hx), mul_zero]
  have memhv : ∀ j I, MemLp (hsD j (v I)) 2 volume := fun j I ↦
    mem (continuous_hsD (hvC I) j) fun x hx ↦ hsD_eq_zero_of_eventuallyEq_zero (hvz I x hx) j
  have hPvz : ∀ I x, x ∉ tsupport u → diffOp A a (v I) x = 0 := by
    intro I x hx
    simp only [diffOp]
    refine Finset.sum_eq_zero fun α _ ↦ ?_
    rw [pderiv_eq_dT, dT_congr_of_eventuallyEq (hvz I x hx)]
    simp [dT]
  have hPvC : ∀ I, Continuous (fun x ↦ diffOp A a (v I) x) := by
    intro I
    simp only [diffOp]
    exact continuous_finsetSum _ fun α hα ↦ (ha α hα).continuous.mul
      (contDiff_pderiv (hvC I) α).continuous
  have memPv : ∀ I, MemLp (fun x ↦ ‖diffOp A a (v I) x‖) 2 volume := fun I ↦
    mem (hPvC I).norm fun x hx ↦ by rw [hPvz I x hx, norm_zero]
  have contV : ∀ j, Continuous (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD j (v I) x ^ 2)) :=
    fun j ↦ (continuous_finsetSum _ fun I _ ↦ (continuous_hsD (hvC I) j).pow 2).sqrt
  have contVP : Continuous (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (v I) x‖ ^ 2)) :=
    (continuous_finsetSum _ fun I _ ↦ (hPvC I).norm.pow 2).sqrt
  have hV1mem : MemLp (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD m (v I) x ^ 2)) 2 volume :=
    mem (contV m) fun x hx ↦ by
      simp [hsD_eq_zero_of_eventuallyEq_zero (hvz _ x hx)]

  set R3 : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ ∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1),
      (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x)
    with hR3
  have memR3 : MemLp R3 2 volume := memLp_sum_mul _ _ _ fun ij _ ↦ memg _
  have h3 : wN χ u (m + k) ≤
      l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD m (v I) x ^ 2)) + l2n R3 := by
    refine (l2Norm_le_of_abs_le (hV1mem.add memR3) (memg (m + k)).aestronglyMeasurable fun x ↦ ?_).trans
      (l2Norm_add_le_alt hV1mem memR3)
    rw [abs_of_nonneg (by have := hsD_nonneg (m + k) u x; have := (h01 x).1; positivity)]
    exact weight_hsD_add_le hu hχ h01 hK0 hK (k := k) (s := s) (m := m) le_rfl le_rfl x
  have hR3le : l2n R3 ≤ ∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1),
      (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k) :=
    l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _

  have hsum_eq : ∀ j, l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD j (v I) x ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD j (v I)) ^ 2) := fun j ↦
    l2Norm_sqrt_sum_sq_eq _ fun I ↦ memhv j I
  have hP_eq : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (v I) x‖ ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (fun x ↦ ‖diffOp A a (v I) x‖) ^ 2) :=
    l2Norm_sqrt_sum_sq_eq (fun I x ↦ ‖diffOp A a (v I) x‖) memPv
  have h4 : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD m (v I) x ^ 2)) ≤
      C₀ * (l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (v I) x‖ ^ 2)) +
        ∑ j ∈ range m, l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD j (v I) x ^ 2))) := by
    rw [hsum_eq m, hP_eq]
    simp only [hsum_eq]
    calc Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD m (v I)) ^ 2)
        ≤ Real.sqrt (∑ I : Fin k → Fin n, (C₀ * (l2n (fun x ↦ ‖diffOp A a (v I) x‖) +
            ∑ j ∈ range m, l2n (hsD j (v I)))) ^ 2) :=
          sqrt_sum_sq_mono fun I ↦ ⟨l2Norm_nonneg_alt _, hE (v I) (hvC I) (hvcs I) (hvU I)⟩
      _ = C₀ * Real.sqrt (∑ I : Fin k → Fin n, (l2n (fun x ↦ ‖diffOp A a (v I) x‖) +
            ∑ j ∈ range m, l2n (hsD j (v I))) ^ 2) := by
          rw [sqrt_sum_sq_const_mul, abs_of_nonneg hC₀]
      _ ≤ C₀ * (Real.sqrt (∑ I : Fin k → Fin n, l2n (fun x ↦ ‖diffOp A a (v I) x‖) ^ 2) +
            ∑ j ∈ range m, Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD j (v I)) ^ 2)) :=
          mul_le_mul_of_nonneg_left ((sqrt_sum_sq_add_le
            (fun I ↦ l2n (fun x ↦ ‖diffOp A a (v I) x‖))
            (fun I ↦ ∑ j ∈ range m, l2n (hsD j (v I)))).trans
            (add_le_add le_rfl (sqrt_sum_sq_sum_le (range m) (fun j I ↦ l2n (hsD j (v I)))))) hC₀

  have h1 : ∀ j ∈ range m, l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD j (v I) x ^ 2)) ≤
      ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k) := by
    intro j hj
    have hjm : j < m := Finset.mem_range.1 hj
    have memR : MemLp (fun x ↦ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
        (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x)) 2 volume :=
      memLp_sum_mul _ _ _ fun ij _ ↦ memg _
    refine (l2Norm_le_of_abs_le memR (contV j).aestronglyMeasurable fun x ↦ ?_).trans
      (l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_sum_hsD_weight_le hu hχ h01 hK0 hK (L₀ := m) hjm.le (by omega) x

  have h2 : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (v I) x‖ ^ 2)) ≤
      (∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
          (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * wN χ u (mabs α + ij.2)) +
        (∑ α ∈ A, A₀ * ∑ ij ∈ (antidiagonal (mabs α)).filter (fun ij ↦ 0 < ij.1),
          ((mabs α).choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) := by
    have memG1 : MemLp (fun x ↦ ∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
          (χ x ^ (mabs α + ij.2) * hsD (mabs α + ij.2) u x)) 2 volume :=
      memLp_finsetSum A fun α _ ↦ memLp_sum_mul _ _ _ fun ij _ ↦ memg _
    have memG2 : MemLp (fun x ↦ ∑ α ∈ A, A₀ * ∑ ij ∈ (antidiagonal (mabs α)).filter
        (fun ij ↦ 0 < ij.1), ((mabs α).choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
          (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x)) 2 volume :=
      memLp_finsetSum A fun α _ ↦ (memLp_sum_mul _ _ _ fun ij _ ↦ memg _).const_mul A₀
    refine (l2Norm_le_of_abs_le (memG1.add memG2) contVP.aestronglyMeasurable fun x ↦ ?_).trans
      ((l2Norm_add_le_alt memG1 memG2).trans (add_le_add ?_ ?_))
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact sqrt_sum_diffOp_weight_le ha hA₀0 hA₀ hA hu hU hPu hχ h01 hχU' hCa hMa hcoef hK0 hK
        le_rfl (by omega) hs1 x
    · refine (l2Norm_finset_sum_le A _ fun α _ ↦ memLp_sum_mul _ _ _ fun ij _ ↦ memg _).trans
        (Finset.sum_le_sum fun α _ ↦ ?_)
      exact l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _
    · refine (l2Norm_finset_sum_le A _ fun α _ ↦
        (memLp_sum_mul _ _ _ fun ij _ ↦ memg _).const_mul A₀).trans
        (Finset.sum_le_sum fun α _ ↦ ?_)
      rw [l2Norm_const_mul, abs_of_nonneg hA₀0]
      exact mul_le_mul_of_nonneg_left
        (l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _) hA₀0
  calc wN χ u (m + k)
      ≤ l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD m (v I) x ^ 2)) + l2n R3 := h3
    _ ≤ C₀ * (l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, ‖diffOp A a (v I) x‖ ^ 2)) +
          ∑ j ∈ range m, l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD j (v I) x ^ 2))) +
        ∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1),
          (m.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k) := add_le_add h4 hR3le
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add h2 (Finset.sum_le_sum h1)) hC₀) le_rfl

theorem sum_antidiagonal_choose_eq (j : ℕ) :
    ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) = 2 ^ j := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact_mod_cast Nat.sum_range_choose j

theorem sum_choose_weight_le {j P k : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ antidiagonal j)
    {K B L : ℝ} (hK0 : 0 ≤ K) (hB0 : 0 ≤ B) (hL1 : 1 ≤ L) (hP1 : 1 ≤ P) (w : ℕ → ℝ)
    (hw : ∀ ij ∈ S, w (ij.2 + k) ≤ B * L ^ (ij.2 + k) * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k))
    (hidx : ∀ ij ∈ S, ij.2 + k + 1 ≤ P ∧ ij.2 + k + ij.1 ≤ P) :
    ∑ ij ∈ S, (j.choose ij.1 : ℝ) * (K * (P : ℝ) ^ ij.1) * w (ij.2 + k) ≤
      2 ^ j * K * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
  have hT : 0 ≤ B * L ^ (P - 1) * (P : ℝ) ^ P := by
    have : (0 : ℝ) ≤ L := by linarith
    positivity
  calc ∑ ij ∈ S, (j.choose ij.1 : ℝ) * (K * (P : ℝ) ^ ij.1) * w (ij.2 + k)
      ≤ ∑ ij ∈ S, (j.choose ij.1 : ℝ) * K * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
        refine Finset.sum_le_sum fun ij hij ↦ ?_
        obtain ⟨h1, h2⟩ := hidx ij hij
        have hb := powMul_bound_le hB0 hL1 (p := P) (q := ij.2 + k) (i := ij.1) hP1 h1 h2
        have hPi : 0 ≤ (P : ℝ) ^ ij.1 := by positivity
        calc (j.choose ij.1 : ℝ) * (K * (P : ℝ) ^ ij.1) * w (ij.2 + k)
            ≤ (j.choose ij.1 : ℝ) * (K * (P : ℝ) ^ ij.1) *
                (B * L ^ (ij.2 + k) * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k)) := by
              gcongr; exact hw ij hij
          _ = (j.choose ij.1 : ℝ) * K * ((P : ℝ) ^ ij.1 *
                (B * L ^ (ij.2 + k) * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k))) := by ring
          _ ≤ _ := by gcongr
    _ = (∑ ij ∈ S, (j.choose ij.1 : ℝ)) * K * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ 2 ^ j * K * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
        gcongr
        rw [← sum_antidiagonal_choose_eq j]
        exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ ↦ by positivity

theorem sum_coef_weight_le {k P d : ℕ} (hP1 : 1 ≤ P) (hdk : d + k ≤ P) {Ca Ma B L : ℝ}
    (hCa : 0 ≤ Ca) (hMa : 0 ≤ Ma) (hB0 : 0 ≤ B) (hL1 : 1 ≤ L) (hML : 2 * Ma ≤ L) (w : ℕ → ℝ)
    (hw : ∀ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
      w (d + ij.2) ≤ B * L ^ (d + ij.2) * ((d + ij.2 : ℕ) : ℝ) ^ (d + ij.2)) :
    ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * w (d + ij.2) ≤
      2 * Ca * Ma * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
  have hL0 : 0 < L := by linarith
  have hr0 : 0 ≤ Ma / L := div_nonneg hMa hL0.le
  have hr : Ma / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
  have hT : 0 ≤ B * L ^ P * (P : ℝ) ^ P := by positivity
  calc ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * w (d + ij.2)
      ≤ ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
          Ca * (B * L ^ P * (P : ℝ) ^ P) * (Ma / L) ^ ij.1 := by
        refine Finset.sum_le_sum fun ij hij ↦ ?_
        have h1 : ij.1 + ij.2 = k := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have hb := coefTerm_le hB0 hL1 hMa (p := P) (k := k) (i := ij.1) (q := d + ij.2) hP1
          (by omega) (by omega)
        calc (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * w (d + ij.2)
            ≤ (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) *
                (B * L ^ (d + ij.2) * ((d + ij.2 : ℕ) : ℝ) ^ (d + ij.2)) := by
              gcongr; exact hw ij hij
          _ = Ca * ((k.choose ij.1 : ℝ) * (Ma ^ ij.1 * ij.1.factorial) *
                (B * L ^ (d + ij.2) * ((d + ij.2 : ℕ) : ℝ) ^ (d + ij.2))) := by ring
          _ ≤ Ca * (B * L ^ P * (P : ℝ) ^ P * (Ma / L) ^ ij.1) := by gcongr
          _ = _ := by ring
    _ = Ca * (B * L ^ P * (P : ℝ) ^ P) *
          ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1), (Ma / L) ^ ij.1 := by
        rw [Finset.mul_sum]
    _ ≤ Ca * (B * L ^ P * (P : ℝ) ^ P) * (2 * (Ma / L)) := by
        gcongr; exact sum_filter_antidiagonal_pow_le hr0 hr k
    _ = 2 * Ca * Ma * (B * L ^ (P - 1) * (P : ℝ) ^ P) := by
        have hLP : L ^ P = L ^ (P - 1) * L := by rw [← pow_succ, Nat.sub_add_cancel hP1]
        rw [hLP]
        field_simp

theorem weighted_derivative_bound {m : ℕ} (hm : 1 ≤ m) {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (ha : ∀ α ∈ A, ContDiff ℝ ∞ (a α))
    {A₀ : ℝ} (hA₀0 : 0 ≤ A₀) (hA₀ : ∀ α ∈ A, ∀ x, ‖a α x‖ ≤ A₀) (hA : ∀ α ∈ A, mabs α ≤ m)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u) (hu_c : HasCompactSupport u)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hPu : ∀ x ∈ U, diffOp A a u x = 0)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχU : tsupport χ ⊆ U)
    {Ca Ma : ℝ} (hCa : 0 ≤ Ca) (hMa : 0 ≤ Ma)
    (hcoef : ∀ α ∈ A, ∀ x ∈ U, ∀ i, hsD i (a α) x ≤ Ca * Ma ^ i * i.factorial)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hE : ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ U → l2n (hsD m v) ≤
        C₀ * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ range m, l2n (hsD j v)))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i)) :
    ∃ B L : ℝ, 0 ≤ B ∧ 1 ≤ L ∧ ∀ p : ℕ, wN χ u p ≤ B * L ^ p * (p : ℝ) ^ p := by
  classical
  set B : ℝ := ∑ q ∈ range m, wN χ u q with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun q _ ↦ wN_nonneg _ _ _
  set Q : ℝ := C₀ * ((A.card : ℝ) * (2 * Ca * Ma) + (A.card : ℝ) * (A₀ * (2 ^ m * K)) +
    (m : ℝ) * (2 ^ m * K)) + 2 ^ m * K with hQ
  set L : ℝ := max (max 1 (2 * Ma)) Q with hL
  have hL1 : 1 ≤ L := le_max_of_le_left (le_max_left _ _)
  have hML : 2 * Ma ≤ L := le_max_of_le_left (le_max_right _ _)
  have hQL : Q ≤ L := le_max_right _ _
  refine ⟨B, L, hB0, hL1, fun p ↦ ?_⟩
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  rcases lt_or_ge p m with hpm | hpm
  · have h1 : wN χ u p ≤ B :=
      Finset.single_le_sum (fun q _ ↦ wN_nonneg χ u q) (Finset.mem_range.2 hpm)
    have h2 : 1 ≤ L ^ p * (p : ℝ) ^ p := by
      refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) ?_
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · exact one_le_pow₀ (by exact_mod_cast hp)
    calc wN χ u p ≤ B := h1
      _ ≤ B * (L ^ p * (p : ℝ) ^ p) := le_mul_of_one_le_right hB0 h2
      _ = B * L ^ p * (p : ℝ) ^ p := by ring
  · obtain ⟨k, rfl⟩ : ∃ k, p = m + k := ⟨p - m, by omega⟩
    set P := m + k with hP
    have hP1 : 1 ≤ P := by omega
    set T := B * L ^ (P - 1) * (P : ℝ) ^ P with hT
    have hT0 : 0 ≤ T := by
      have : (0 : ℝ) ≤ L := by linarith
      positivity
    have ih' : ∀ q, q < P → wN χ u q ≤ B * L ^ q * (q : ℝ) ^ q := fun q hq ↦ ih q hq
    have hstep := wN_step hm ha hA₀0 hA₀ hA hu hu_c hU hPu hχ h01 hχU hCa hMa hcoef hC₀ hE hK0
      hK k
    have hS1 : (∑ α ∈ A, ∑ ij ∈ (antidiagonal k).filter (fun ij ↦ 0 < ij.1),
        (k.choose ij.1 : ℝ) * (Ca * Ma ^ ij.1 * ij.1.factorial) * wN χ u (mabs α + ij.2)) ≤
        (A.card : ℝ) * (2 * Ca * Ma * T) := by
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun α hα ↦ ?_
      refine sum_coef_weight_le hP1 (by have := hA α hα; omega) hCa hMa hB0 hL1 hML _
        fun ij hij ↦ ih' _ ?_
      have h1 : ij.1 + ij.2 = k := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
      have h2 := (Finset.mem_filter.1 hij).2
      have := hA α hα
      omega
    have hS2 : (∑ α ∈ A, A₀ * ∑ ij ∈ (antidiagonal (mabs α)).filter (fun ij ↦ 0 < ij.1),
        ((mabs α).choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) ≤
        (A.card : ℝ) * (A₀ * (2 ^ m * K * T)) := by
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun α hα ↦ ?_
      have hαm := hA α hα
      refine mul_le_mul_of_nonneg_left ?_ hA₀0
      refine (sum_choose_weight_le (Finset.filter_subset _ _) hK0 hB0 hL1 hP1 _
        (fun ij hij ↦ ih' _ ?_) fun ij hij ↦ ?_).trans ?_
      · have h1 : ij.1 + ij.2 = mabs α := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have h2 := (Finset.mem_filter.1 hij).2
        omega
      · have h1 : ij.1 + ij.2 = mabs α := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have h2 := (Finset.mem_filter.1 hij).2
        constructor <;> omega
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hαm) hK0) hT0
    have hS3 : (∑ j ∈ range m, ∑ ij ∈ antidiagonal j,
        (j.choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) ≤
        (m : ℝ) * (2 ^ m * K * T) := by
      have := Finset.sum_le_card_nsmul (range m) (fun j ↦ ∑ ij ∈ antidiagonal j,
        (j.choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k))
        (2 ^ m * K * T) fun j hj ↦ by
          have hjm := Finset.mem_range.1 hj
          refine (sum_choose_weight_le (subset_refl _) hK0 hB0 hL1 hP1 _
            (fun ij hij ↦ ih' _ ?_) fun ij hij ↦ ?_).trans ?_
          · have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
            omega
          · have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
            constructor <;> omega
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) hjm.le) hK0) hT0
      simpa [nsmul_eq_mul] using this
    have hS4 : (∑ ij ∈ (antidiagonal m).filter (fun ij ↦ 0 < ij.1),
        (m.choose ij.1 : ℝ) * (K * ((m + k : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) ≤
        2 ^ m * K * T := by
      refine sum_choose_weight_le (Finset.filter_subset _ _) hK0 hB0 hL1 hP1 _
        (fun ij hij ↦ ih' _ ?_) fun ij hij ↦ ?_
      · have h1 : ij.1 + ij.2 = m := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have h2 := (Finset.mem_filter.1 hij).2
        omega
      · have h1 : ij.1 + ij.2 = m := mem_antidiagonal.1 (Finset.mem_filter.1 hij).1
        have h2 := (Finset.mem_filter.1 hij).2
        constructor <;> omega
    calc wN χ u P ≤ _ := hstep
      _ ≤ C₀ * ((A.card : ℝ) * (2 * Ca * Ma * T) + (A.card : ℝ) * (A₀ * (2 ^ m * K * T)) +
            (m : ℝ) * (2 ^ m * K * T)) + 2 ^ m * K * T := by
          gcongr
      _ = Q * T := by simp only [hQ]; ring
      _ ≤ L * T := by gcongr
      _ = B * L ^ P * (P : ℝ) ^ P := by
          have hLP : L ^ P = L * L ^ (P - 1) := by rw [← pow_succ', Nat.sub_add_cancel hP1]
          rw [hLP, hT]; ring

end

end GroundTheory.Automorphic.Sobolev
