import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.GaussMul

open Filter

theorem norm_sum_lt_of_ultra {E ι : Type} [SeminormedAddCommGroup E] [IsUltrametricDist E] (s : Finset ι)
    (f : ι → E) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem exists_eq_sup {f : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hle : ∀ n, f n ≤ M)
    (hsup : ∀ r : ℝ, 0 ≤ r → (∀ n, f n ≤ r) → M ≤ r) (ht : Tendsto f atTop (nhds 0)) : ∃ n, f n = M := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ n, f n < M := fun n => lt_of_le_of_ne (hle n) (hne n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hM)))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have h1 : M ≤ max (M / 2) (f k) := hsup _ ((half_pos hM).le.trans (le_max_left _ _)) fun n => by
    by_cases hn : n < N + 1
    · exact (hk n (Finset.mem_range.2 hn)).trans (le_max_right _ _)
    · exact (hN n (by omega)).le.trans (le_max_left _ _)
  exact absurd h1 (not_le.2 (max_lt (half_lt_self hM) (hlt k)))

theorem gauss {D : Type} [NormedRing D] [IsUltrametricDist D] (hm : ∀ x y : D, ‖x * y‖ = ‖x‖ * ‖y‖) {ρ : ℝ}
    (hρ : 0 < ρ) (p q : ℕ → D) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hp : ∀ n, ‖p n‖ * ρ ^ n ≤ P)
    (hq : ∀ n, ‖q n‖ * ρ ^ n ≤ Q) (hp0 : ∃ n, ‖p n‖ * ρ ^ n = P) (hq0 : ∃ n, ‖q n‖ * ρ ^ n = Q) :
    ∃ N, ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, p x.1 * q x.2‖ * ρ ^ N = P * Q := by
  classical
  set n₀ := Nat.find hp0
  set m₀ := Nat.find hq0
  have hn₀ : ‖p n₀‖ * ρ ^ n₀ = P := Nat.find_spec hp0
  have hm₀ : ‖q m₀‖ * ρ ^ m₀ = Q := Nat.find_spec hq0
  refine ⟨n₀ + m₀, ?_⟩
  have hρN : 0 < ρ ^ (n₀ + m₀) := pow_pos hρ _
  have hmem : (n₀, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hdom : ‖p n₀ * q m₀‖ * ρ ^ (n₀ + m₀) = P * Q := by
    rw [hm, pow_add, ← hn₀, ← hm₀]; ring
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n₀ + m₀)).erase (n₀, m₀), p x.1 * q x.2‖ < P * Q / ρ ^ (n₀ + m₀) := by
    refine norm_sum_lt_of_ultra _ _ (div_pos (mul_pos hP hQ) hρN) fun x hx => ?_
    rw [lt_div_iff₀ hρN]
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have e : ‖p x.1 * q x.2‖ * ρ ^ (n₀ + m₀) = (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) := by
      rw [hm, ← hx, pow_add]; ring
    rw [e]
    have h1 : 0 ≤ ‖p x.1‖ * ρ ^ x.1 := by positivity
    have h2 : 0 ≤ ‖q x.2‖ * ρ ^ x.2 := by positivity
    by_cases h : x.1 < n₀
    · have hlt : ‖p x.1‖ * ρ ^ x.1 < P := lt_of_le_of_ne (hp _) (Nat.find_min hp0 h)
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ (‖p x.1‖ * ρ ^ x.1) * Q :=
            mul_le_mul_of_nonneg_left (hq _) h1
        _ < P * Q := mul_lt_mul_of_pos_right hlt hQ
    · have h' : x.2 < m₀ := by
        by_contra h''
        apply hne
        ext <;> simp <;> omega
      have hlt : ‖q x.2‖ * ρ ^ x.2 < Q := lt_of_le_of_ne (hq _) (Nat.find_min hq0 h')
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ P * (‖q x.2‖ * ρ ^ x.2) :=
            mul_le_mul_of_nonneg_right (hp _) h2
        _ < P * Q := mul_lt_mul_of_pos_left hlt hP
  have hdom' : ‖p n₀ * q m₀‖ = P * Q / ρ ^ (n₀ + m₀) := by
    rw [eq_div_iff hρN.ne', hdom]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdom']; exact hrest.ne'), hdom',
    max_eq_left hrest.le, div_mul_cancel₀ _ hρN.ne']

end GlobalTheory.BSP.GaussMul

namespace GlobalTheory.BSP.GaussMul

theorem norm_mul_disc (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x y : bk.DS ρ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 hρ1
  haveI : IsUltrametricDist (Disc l (0 : Wq l bk.a) 1) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) 0 1).1
  have hm0 := (GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk).1
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ0

  have step1 : ∀ s t : bk.S, ‖toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t‖ =
      ‖toDisc l (X : bk.S) ρ s‖ * ‖toDisc l (X : bk.S) ρ t‖ := by
    intro s t
    rcases eq_or_ne (toDisc l (X : bk.S) ρ s) 0 with hu | hu
    · simp [hu]
    rcases eq_or_ne (toDisc l (X : bk.S) ρ t) 0 with hv | hv
    · simp [hv]
    have hP : 0 < ‖toDisc l (X : bk.S) ρ s‖ := norm_pos_iff.2 hu
    have hQ : 0 < ‖toDisc l (X : bk.S) ρ t‖ := norm_pos_iff.2 hv
    obtain ⟨N, hN⟩ := gauss hm0 hρ (fun n => a n (toDisc l (X : bk.S) ρ s)) (fun n => a n (toDisc l (X : bk.S) ρ t))
      hP hQ (fun n => ha2 n _) (fun n => ha2 n _)
      (exists_eq_sup hP (fun n => ha2 n _) (ha3 _) (ha4 _)) (exists_eq_sup hQ (fun n => ha2 n _) (ha3 _) (ha4 _))
    have hconv : a N (toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, a x.1 (toDisc l (X : bk.S) ρ s) * a x.2 (toDisc l (X : bk.S) ρ t) := by
      rw [← map_mul, ha1, coeff_mul, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, ha1, ha1]
    refine le_antisymm (norm_mul_le _ _) ?_
    rw [← hN, ← hconv]
    exact ha2 N _

  have hlm := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ).2.1
  have hl0 : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.2 hl.out.pos
  have hlpow : ∀ (n : ℕ) (z : bk.DS ρ), ‖z * ((l : ℕ) : bk.DS ρ) ^ n‖ = ‖z‖ / (l : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← mul_assoc, mul_comm _ ((l : ℕ) : bk.DS ρ), hlm, ih, pow_succ, div_div]
  have hpre : ∀ p : PreDisc l (X : bk.S) ρ, ∃ (n : ℕ) (s : bk.S),
      ofPre l (X : bk.S) ρ p * ((l : ℕ) : bk.DS ρ) ^ n = toDisc l (X : bk.S) ρ s := by
    intro p
    obtain ⟨n, s, h⟩ := IsLocalization.Away.surj ((l : ℕ) : bk.S) p
    refine ⟨n, s, ?_⟩
    have h' := congrArg (ofPre l (X : bk.S) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at h'
    exact h'
  have step2 : ∀ p q : PreDisc l (X : bk.S) ρ, ‖ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q‖ =
      ‖ofPre l (X : bk.S) ρ p‖ * ‖ofPre l (X : bk.S) ρ q‖ := by
    intro p q
    obtain ⟨n, s, hs⟩ := hpre p
    obtain ⟨m, t, ht⟩ := hpre q
    have e : ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q * ((l : ℕ) : bk.DS ρ) ^ (n + m) =
        toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t := by
      rw [← hs, ← ht, pow_add]; ring
    have h1 := hlpow (n + m) (ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q)
    rw [e, step1, ← hs, ← ht, hlpow, hlpow, pow_add, div_mul_div_comm] at h1
    exact ((div_left_inj' (by positivity)).1 h1).symm
  exact (denseRange_ofPre l (X : bk.S) ρ).induction_on₂ (p := fun x y : bk.DS ρ => ‖x * y‖ = ‖x‖ * ‖y‖)
    (isClosed_eq (continuous_norm.comp (continuous_fst.mul continuous_snd))
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))) step2 x y

theorem norm_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ :=
  fun l _ K bk ρ h0 h1 x y => norm_mul_disc l K bk ρ h0 h1 x y

end GlobalTheory.BSP.GaussMul
