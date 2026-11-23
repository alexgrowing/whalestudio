import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

section ThQ

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem thq_add_le {x y : C} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem thq_pow_sub (b d : C) (hb : ‖b‖ ≤ 1) (hbd : ‖b + d‖ ≤ 1) (m : ℕ) :
    ∃ e : C, ‖e‖ ≤ ‖d‖ ∧ (b + d) ^ (m + 1) - b ^ (m + 1) = d * (((m + 1 : ℕ) : C) * b ^ m + e) := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨d * ((m + 1 : ℕ) : C) * b ^ m + (b + d) * e, ?_, ?_⟩
    · apply thq_add_le
      · rw [norm_mul, norm_mul, norm_pow]
        have h1 : ‖((m + 1 : ℕ) : C)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one C (m + 1)
        have h2 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖d‖ * ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖d‖ * 1 * 1 := by gcongr
          _ = ‖d‖ := by ring
      · rw [norm_mul]
        calc ‖b + d‖ * ‖e‖ ≤ 1 * ‖d‖ := by gcongr
          _ = ‖d‖ := one_mul _
    · have h3 : (b + d) ^ (m + 1 + 1) - b ^ (m + 1 + 1)
          = (b + d) * ((b + d) ^ (m + 1) - b ^ (m + 1)) + d * b ^ (m + 1) := by ring
      rw [h3, h]
      push_cast
      ring

theorem thq_step {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) {a b : C}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {r : ℝ} (hab : ‖a - b‖ ≤ r) (hr : r ≤ ‖P‖) :
    ‖(P * a + a ^ q) - (P * b + b ^ q)‖ ≤ ‖P‖ * r := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
  obtain ⟨e, he, h⟩ := thq_pow_sub b (a - b) hb (by simpa using ha) m
  rw [add_sub_cancel] at h
  have h1 : (P * a + a ^ (m + 1)) - (P * b + b ^ (m + 1))
      = P * (a - b) + (a - b) * (((m + 1 : ℕ) : C) * b ^ m + e) := by
    rw [← h]; ring
  rw [h1]
  apply thq_add_le
  · rw [norm_mul]; gcongr
  · have h2 : ‖((m + 1 : ℕ) : C) * b ^ m + e‖ ≤ ‖P‖ := by
      apply thq_add_le
      · rw [norm_mul, norm_pow]
        have h3 : ‖b‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
        calc ‖((m + 1 : ℕ) : C)‖ * ‖b‖ ^ m ≤ ‖P‖ * 1 := by gcongr
          _ = ‖P‖ := mul_one _
      · exact he.trans (hab.trans hr)
    rw [norm_mul, mul_comm]
    gcongr

theorem thq_ball {P : C} {q : ℕ} (hP : ‖P‖ ≤ 1) {a : C} (ha : ‖a‖ ≤ 1) : ‖P * a + a ^ q‖ ≤ 1 := by
  apply thq_add_le
  · rw [norm_mul]
    calc ‖P‖ * ‖a‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem thq_iter {P : C} {q : ℕ} (hq : 2 ≤ q) (hqP : ‖(q : C)‖ ≤ ‖P‖) (hP : ‖P‖ ≤ 1) (n : ℕ) :
    ∀ (a b : C) (r : ℝ), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a - b‖ ≤ r → r ≤ ‖P‖ →
      ‖ltIter P q n a - ltIter P q n b‖ ≤ ‖P‖ ^ n * r := by
  induction n with
  | zero => intro a b r _ _ hab _; simpa [ltIter] using hab
  | succ n ih =>
    intro a b r ha hb hab hr
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hab
    have h1 := thq_step hq hqP ha hb hab hr
    have h2 : ‖P‖ * r ≤ ‖P‖ := by
      calc ‖P‖ * r ≤ 1 * r := by gcongr
        _ = r := one_mul _
        _ ≤ ‖P‖ := hr
    have h3 := ih _ _ _ (thq_ball hP ha) (thq_ball hP hb) h1 h2
    have e1 : ∀ x : C, ltIter P q (n + 1) x = ltIter P q n (P * x + x ^ q) := fun x => by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e1]
    calc _ ≤ ‖P‖ ^ n * (‖P‖ * r) := h3
      _ = ‖P‖ ^ (n + 1) * r := by ring

theorem thq_map {B : Type} [CommRing B] (θ : B →+* C) (ϖ : B) (q n : ℕ) (x : B) :
    θ (ltIter ϖ q n x) = ltIter (θ ϖ) q n (θ x) := by
  induction n generalizing x with
  | zero => simp [ltIter]
  | succ n ih =>
    have e1 : ltIter ϖ q (n + 1) x = ltIter ϖ q n (ϖ * x + x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    have e2 : ltIter (θ ϖ) q (n + 1) (θ x) = ltIter (θ ϖ) q n (θ ϖ * θ x + θ x ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, e2, ih]
    simp

theorem thq_tower {P : C} {q : ℕ} {w : ℕ → C} (h0 : w 0 = 0)
    (hw : ∀ n, w (n + 1) ^ q + P * w (n + 1) = w n) (n : ℕ) : ltIter P q n (w n) = 0 := by
  induction n with
  | zero => simpa [ltIter] using h0
  | succ n ih =>
    have e1 : ltIter P q (n + 1) (w (n + 1)) = ltIter P q n (P * w (n + 1) + w (n + 1) ^ q) := by
      simp only [ltIter, Function.iterate_succ_apply]
    rw [e1, add_comm, hw, ih]

end ThQ

theorem theta_eq_zero_of_congr_torsion : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  intro B _ S F ϖ C _ _ _ θ hS _ hlt q hq hqP v hv w h0 hw hvw Q hQ hQn
  have hP : ‖θ ϖ‖ ≤ 1 := hlt.le
  have hwb : ∀ n, ‖w n‖ ≤ 1 := fun n => by
    have h1 : w n = θ (v n) + -(θ (v n) - w n) := by ring
    rw [h1]
    exact thq_add_le (hS _ (hv n)) (by rw [norm_neg]; exact (hvw n).trans hP)
  have hb : ∀ n, ‖θ Q‖ ≤ ‖θ ϖ‖ ^ (n + 1) := fun n => by
    obtain ⟨a, ha, hQa⟩ := hQn n
    have h1 : θ Q = ltIter (θ ϖ) q n (θ (v n)) + θ ϖ ^ (n + 1) * θ a := by
      have h2 : θ (Q - ltIter ϖ q n (v n)) = θ (ϖ ^ (n + 1) * a) := congrArg θ hQa
      rw [map_sub, thq_map, map_mul, map_pow] at h2
      rw [← h2]; ring
    have h3 := thq_iter hq hqP hP n (θ (v n)) (w n) _ (hS _ (hv n)) (hwb n) (hvw n) le_rfl
    rw [thq_tower h0 hw n, sub_zero] at h3
    rw [h1]
    apply thq_add_le
    · calc _ ≤ ‖θ ϖ‖ ^ n * ‖θ ϖ‖ := h3
        _ = ‖θ ϖ‖ ^ (n + 1) := by ring
    · rw [norm_mul, norm_pow]
      calc ‖θ ϖ‖ ^ (n + 1) * ‖θ a‖ ≤ ‖θ ϖ‖ ^ (n + 1) * 1 := by
            gcongr
            exact hS _ ha
        _ = ‖θ ϖ‖ ^ (n + 1) := mul_one _
  have hlim : Filter.Tendsto (fun n : ℕ => ‖θ ϖ‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt).comp (Filter.tendsto_add_atTop_nat 1)
  have h0' : ‖θ Q‖ ≤ 0 := ge_of_tendsto' hlim hb
  exact norm_le_zero_iff.mp h0'

end GlobalTheory.CompanionTheory.LTPer
