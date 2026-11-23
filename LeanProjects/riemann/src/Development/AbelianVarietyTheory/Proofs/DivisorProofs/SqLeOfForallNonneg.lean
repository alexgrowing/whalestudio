import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Bdd

theorem sq_le_of_forall_nonneg {A B D : ℤ} (h : ∀ s t : ℤ, 0 ≤ s * s * A + 2 * (s * t) * B + t * t * D) :
    B * B ≤ A * D := by
  have hA : 0 ≤ A := by simpa using h 1 0
  have hD : 0 ≤ D := by simpa using h 0 1
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    have h2 := h (-B * (D + 1)) 1
    have : B = 0 := by
      by_contra hB
      have hB2 : 1 ≤ B * B := by nlinarith [mul_self_pos.2 hB]
      nlinarith
    subst this; simp
  · have h1 := h B (-A)
    nlinarith

theorem seq_le (F : ℕ → ℤ) (h0 : ∀ k, 0 ≤ F k) (hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2)) (d : ℕ)
    (p : ℕ → ℤ) (hd : p d = 1) (hrec : ∑ i ∈ Finset.range (d + 1), p i * F i = 0) :
    F 1 ≤ (∑ i ∈ Finset.range (d + 1), |p i|) * F 0 := by
  set C := ∑ i ∈ Finset.range (d + 1), |p i| with hCdef
  have hC1 : 1 ≤ C := by
    have := Finset.single_le_sum (f := fun i => |p i|) (fun i _ => abs_nonneg (p i)) (Finset.self_mem_range_succ d)
    simpa [hd] using this
  by_contra hlt
  push_neg at hlt
  have hF0 : 0 < F 0 := by
    rcases (h0 0).eq_or_lt with h | h
    · have := hlc 0
      rw [← h] at this hlt
      have h1 : F 1 * F 1 ≤ 0 := by simpa using this
      have : F 1 = 0 := by nlinarith [mul_self_nonneg (F 1)]
      simp [this] at hlt
    · exact h
  have hF1 : C * F 0 < F 1 := hlt
  have key : ∀ k, 0 < F k ∧ F 1 * F k ≤ F 0 * F (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hF0, by rw [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hpos : 0 < F (k + 1) := by
        have : 0 < F 1 * F k := mul_pos (by nlinarith) hk
        nlinarith
      refine ⟨hpos, ?_⟩
      have h2 := hlc k
      have h3 : F 1 * F k * F (k + 1) ≤ F 0 * F (k + 1) * F (k + 1) := mul_le_mul_of_nonneg_right hk' hpos.le
      have h4 : F k * (F 1 * F (k + 1)) ≤ F k * (F 0 * F (k + 2)) := by nlinarith
      exact le_of_mul_le_mul_left h4 hk
  have inc : ∀ k, C * F k < F (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := key k
    have : F 0 * (C * F k) < F 0 * F (k + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hF0.le
  have mono : Monotone F := monotone_nat_of_le_succ fun k => by
    have := inc k
    have := (key k).1
    nlinarith
  cases d with
  | zero =>
    simp [hd] at hrec
    exact hF0.ne' hrec
  | succ e =>
    rw [Finset.sum_range_succ, hd, one_mul] at hrec
    rw [Finset.sum_range_succ, hd] at hCdef
    have hle : -(∑ i ∈ Finset.range (e + 1), p i * F i) ≤ (∑ i ∈ Finset.range (e + 1), |p i|) * F e := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 : -(p i * F i) ≤ |p i| * F i := by
        have := neg_abs_le (p i)
        nlinarith [h0 i]
      exact h1.trans (mul_le_mul_of_nonneg_left (mono hi') (abs_nonneg _))
    have he := inc e
    have hpe := (key e).1
    have : F (e + 1) = -(∑ i ∈ Finset.range (e + 1), p i * F i) := by linarith
    rw [this] at he
    rw [hCdef] at he
    simp only [abs_one] at he
    nlinarith

theorem bddAct_of_isIntegral {O : Type} [CommRing O] (bar : O → O) (hmul : ∀ a b, bar (a * b) = bar a * bar b)
    (hone : bar 1 = 1) (hinv : ∀ a, bar (bar a) = a) (hint : ∀ a : O, IsIntegral ℤ a) : BddAct bar := by
  intro c
  obtain ⟨P, hPm, hP⟩ := hint (bar c * c)
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|, ?_⟩
  intro X _ _ _ β hβ hpsd x
  have hpow : ∀ k, bar (c ^ k) = bar c ^ k := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcs : ∀ u v : X, β u v * β u v ≤ β u u * β v v := by
    intro u v
    refine sq_le_of_forall_nonneg fun s t => ?_
    have := hpsd (s • u + t • v)
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hβ.1 v u] at this
    linarith
  have hF : ∀ k, β (c ^ k • x) (c ^ k • x) = β x ((bar c * c) ^ k • x) := by
    intro k
    rw [hβ.2, smul_smul, hpow, mul_pow]
  set F : ℕ → ℤ := fun k => β (c ^ k • x) (c ^ k • x) with hFdef
  have hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2) := by
    intro k
    set y := c ^ k • x
    have e1 : F (k + 1) = β y ((bar c * c) • y) := by
      simp only [hFdef, y, pow_succ', mul_smul]
      rw [hβ.2, smul_smul]
    have e2 : F (k + 2) = β ((bar c * c) • y) ((bar c * c) • y) := by
      have hw : bar (c * c) * (c * c) = bar (bar c * c) * (bar c * c) := by rw [hmul, hmul, hinv]; ring
      show β (c ^ (k + 2) • x) (c ^ (k + 2) • x) = β ((bar c * c) • (c ^ k • x)) ((bar c * c) • (c ^ k • x))
      rw [show c ^ (k + 2) = (c * c) * c ^ k by ring, mul_smul, hβ.2, hβ.2 (bar c * c), smul_smul, smul_smul, hw]
      simp only [mul_smul]
    rw [e1, e2]
    exact hcs _ _
  have hrec : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * F i = 0 := by
    have h0 : β x ((Polynomial.aeval (bar c * c) P) • x) = 0 := by rw [Polynomial.aeval_def, hP, zero_smul, map_zero]
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_smul, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFdef]
    dsimp only
    rw [hF, smul_assoc, map_zsmul, smul_eq_mul]
  have := seq_le F (fun k => hpsd _) hlc P.natDegree P.coeff hPm.coeff_natDegree hrec
  simpa [hFdef] using this

end GlobalTheory.Poinc.Bdd

namespace GlobalTheory.Poinc

open NumberField

theorem bddAct_int_and_cm : BddAct (id : ℤ → ℤ) ∧ ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), BddAct H.bar := by
  refine ⟨Bdd.bddAct_of_isIntegral id (fun _ _ => rfl) rfl (fun _ => rfl) fun a => Algebra.IsIntegral.isIntegral a, ?_⟩
  intro E _ _ _ H
  refine Bdd.bddAct_of_isIntegral H.bar (fun a b => map_mul _ a b) (map_one _) (fun a => ?_)
    fun a => Algebra.IsIntegral.isIntegral a
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.Poinc
