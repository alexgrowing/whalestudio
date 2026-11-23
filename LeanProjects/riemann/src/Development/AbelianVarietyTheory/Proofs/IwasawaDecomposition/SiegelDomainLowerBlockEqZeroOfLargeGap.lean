import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelChain
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelGap

theorem chain {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u) :
    ∀ m : ℕ, ∀ i j : Fin n, (j : ℕ) = i + m → d i ≤ 4 ^ m * d j := by
  first
  | exact @_root_.GlobalTheory.SiegelChain.siegel_chain
  | exact _root_.GlobalTheory.SiegelChain.siegel_chain
  | (apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SiegelChain.siegel_chain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SiegelChain.siegel_chain ..)

theorem chain_le {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u)
    (i j : Fin n) (h : i ≤ j) : d i ≤ 4 ^ n * d j := by
  have h1 := chain hS ((j : ℕ) - i) i j (by have : (i:ℕ) ≤ j := h; omega)
  have hm : (4:ℝ) ^ ((j : ℕ) - i) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc d i ≤ 4 ^ ((j : ℕ) - i) * d j := h1
    _ ≤ 4 ^ n * d j := by gcongr; exact hS.nonneg j

theorem lowerBlock_eq_zero_of_gap : ∀ (n : ℕ) (K c : ℝ), ∃ R : ℝ, 1 ≤ R ∧ ∀ (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), GlobalTheory.RedTh.IsSiegel d u → (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (∀ i j, j < i → v i j = 0) → (∀ i j, |v i j| ≤ c) → (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K) → ∀ k k' : Fin n, (k' : ℕ) = k + 1 → R * d k < d k' → ∀ p q, q ≤ k → k' ≤ p → (u * A.map (Int.cast : ℤ → ℝ) * v) p q = 0 := by
  intro n K c
  set C : ℝ := (n : ℝ) ^ 2 * (|c| + 1) with hC
  set X : ℝ := (|K| + 1) * C ^ 2 with hX
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by positivity
  have h16 : (0:ℝ) ≤ 16 ^ n * X := by positivity
  refine ⟨16 ^ n * X + 1, by linarith, ?_⟩
  intro A d u v hS hd hvu huv hvl hvc hsum k k' hkk' hR p q hqk hkp
  set B : Matrix (Fin n) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set Wm := u * B * v with hW

  have hratio : ∀ s t : Fin n, t ≤ k → k' ≤ s → X * d t < d s := by
    intro s t hts hks
    have h1 := chain_le hS t k hts
    have h2 := chain_le hS k' s hks
    have h4 : (0:ℝ) < 4 ^ n := by positivity
    have hdk := hd k
    have e16 : (16:ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
    have : 4 ^ n * (X * d t) < 4 ^ n * d s := by
      calc 4 ^ n * (X * d t) ≤ 4 ^ n * (X * (4 ^ n * d k)) := by gcongr
        _ = 16 ^ n * X * d k := by rw [e16]; ring
        _ < (16 ^ n * X + 1) * d k := by nlinarith
        _ < d k' := hR
        _ ≤ 4 ^ n * d s := h2
    exact lt_of_mul_lt_mul_left this h4.le

  have hterm : ∀ s t : Fin n, d s / d t * Wm s t ^ 2 ≤ K := by
    intro s t
    have hnn : ∀ a b : Fin n, 0 ≤ d a / d b * Wm a b ^ 2 := fun a b =>
      mul_nonneg (div_nonneg (hd a).le (hd b).le) (sq_nonneg _)
    calc d s / d t * Wm s t ^ 2 ≤ ∑ q, d s / d q * Wm s q ^ 2 :=
          Finset.single_le_sum (f := fun q => d s / d q * Wm s q ^ 2) (fun q _ => hnn s q) (Finset.mem_univ t)
      _ ≤ ∑ p, ∑ q, d p / d q * Wm p q ^ 2 :=
          Finset.single_le_sum (f := fun p => ∑ q, d p / d q * Wm p q ^ 2)
            (fun p _ => Finset.sum_nonneg (fun q _ => hnn p q)) (Finset.mem_univ s)
      _ ≤ K := hsum
  have hWsmall : ∀ s t : Fin n, t ≤ k → k' ≤ s → C * |Wm s t| < 1 := by
    intro s t hts hks
    have hr := hratio s t hts hks
    have hdt := hd t
    have hXr : X < d s / d t := by rw [lt_div_iff₀ hdt]; exact hr
    have h1 : X * Wm s t ^ 2 ≤ K := le_trans (mul_le_mul_of_nonneg_right hXr.le (sq_nonneg _)) (hterm s t)
    have h2 : C ^ 2 * Wm s t ^ 2 < 1 := by
      have hK : K ≤ |K| := le_abs_self K
      by_contra hcon
      push_neg at hcon
      have : (|K| + 1) * 1 ≤ (|K| + 1) * (C ^ 2 * Wm s t ^ 2) := by gcongr
      nlinarith
    have h3 : (C * |Wm s t|) ^ 2 < 1 := by rw [mul_pow, sq_abs]; exact h2
    have h4 : 0 ≤ C * |Wm s t| := by positivity
    nlinarith
  have hrec : B = v * Wm * u := by
    rw [hW]; simp only [← Matrix.mul_assoc]
    rw [hvu, Matrix.one_mul, Matrix.mul_assoc, hvu, Matrix.mul_one]
  have hAzero : ∀ i j : Fin n, k' ≤ i → j ≤ k → A i j = 0 := by
    intro i j hi hj
    have hent : (A i j : ℝ) = ∑ t, (∑ s, v i s * Wm s t) * u t j := by
      have : B i j = (v * Wm * u) i j := by rw [← hrec]
      simpa [hB, Matrix.mul_apply] using this
    have hn : (0:ℝ) < (n:ℝ) ^ 2 := by have := Fin.pos i; positivity
    have key : ∀ s t : Fin n, |v i s * Wm s t * u t j| < 1 / (n:ℝ) ^ 2 := by
      intro s t
      by_cases hs : s < i
      · rw [hvl i s hs]; simp; positivity
      by_cases ht : j < t
      · rw [hS.lower t j ht]; simp; positivity
      push_neg at hs ht
      have hsm := hWsmall s t (le_trans ht hj) (le_trans hi hs)
      have hu1 : |u t j| ≤ 1 := by
        rcases eq_or_lt_of_le ht with h | h
        · rw [h, hS.diag]; simp
        · have := hS.upper t j h; linarith
      have hv1 : |v i s| ≤ |c| + 1 := by
        have := hvc i s; have := le_abs_self c; linarith
      rw [abs_mul, abs_mul]
      calc |v i s| * |Wm s t| * |u t j| ≤ (|c| + 1) * |Wm s t| * 1 := by gcongr
        _ < 1 / (n:ℝ) ^ 2 := by
          rw [lt_div_iff₀ hn]
          have : (|c| + 1) * |Wm s t| * 1 * (n:ℝ) ^ 2 = C * |Wm s t| := by rw [hC]; ring
          linarith
    have hbound : |(A i j : ℝ)| < 1 := by
      rw [hent]
      calc |∑ t, (∑ s, v i s * Wm s t) * u t j| = |∑ t, ∑ s, v i s * Wm s t * u t j| := by
            simp [Finset.sum_mul]
        _ ≤ ∑ t, ∑ s, |v i s * Wm s t * u t j| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => Finset.abs_sum_le_sum_abs _ _)
        _ < ∑ t : Fin n, ∑ s : Fin n, 1 / (n:ℝ) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun t _ =>
              Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun s _ => key s t
        _ = 1 := by
            have : (n:ℝ) ≠ 0 := by have := Fin.pos i; positivity
            simp; field_simp
    have : |A i j| < 1 := by exact_mod_cast hbound
    exact Int.abs_lt_one_iff.mp this
  rw [hW]
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : q < t
  · simp [hvl t q ht]
  push_neg at ht
  have hz : ∑ s, u p s * B s t = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s < p
    · simp [hS.lower p s hs]
    push_neg at hs
    simp [hB, hAzero s t (le_trans hkp hs) (le_trans ht hqk)]
  rw [hz, zero_mul]

end GlobalTheory.SiegelGap
