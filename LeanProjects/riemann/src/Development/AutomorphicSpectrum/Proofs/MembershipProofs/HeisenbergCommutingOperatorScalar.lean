import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariantStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissibleStatement

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ThetaInj

theorem norm_half_lt_one {z : ℂ} (h : ‖z‖ ≤ 1) (h1 : z ≠ 1) : ‖(1 + z) / 2‖ < 1 := by
  have hn : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hre : z.re < 1 := by
    by_contra hc
    push Not at hc
    apply h1
    apply Complex.ext
    · simp only [Complex.one_re]; nlinarith
    · simp only [Complex.one_im]; nlinarith
  have h2 : ‖1 + z‖ ^ 2 < 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    nlinarith
  have h3 : ‖1 + z‖ < 2 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) h2
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  linarith

theorem norm_half_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : ‖(1 + z) / 2‖ ≤ 1 := by
  by_cases h1 : z = 1
  · subst h1; simp
  · exact (norm_half_lt_one h h1).le

theorem charSeries_restrict {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (t : A) [∀ i, Decidable (e i t = 1)] (a : A) :
    ∑' i, (if e i t = 1 then c i else 0) * e i a = 0 := by
  have hb : ∀ (n : ℕ) a i, ‖c i * ((1 + e i t) / 2) ^ n * e i a‖ ≤ ‖c i‖ := by
    intro n a i
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖(1 + e i t) / 2‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_half_le_one (hle i t))
    calc _ ≤ ‖c i‖ * 1 * 1 := by gcongr; exact hle i a
      _ = _ := by ring
  have hn : ∀ (n : ℕ) a, ∑' i, c i * ((1 + e i t) / 2) ^ n * e i a = 0 := by
    intro n
    induction n with
    | zero => simpa using hF
    | succ n ih =>
      intro a
      have : ∀ i, c i * ((1 + e i t) / 2) ^ (n + 1) * e i a
          = (c i * ((1 + e i t) / 2) ^ n * e i a + c i * ((1 + e i t) / 2) ^ n * e i (a + t)) / 2 := by
        intro i; rw [hmul]; ring
      simp only [this]
      rw [tsum_div_const, (Summable.of_norm_bounded hs (hb n a)).tsum_add (Summable.of_norm_bounded hs (hb n (a + t))),
        ih, ih]
      simp
  have hl : Filter.Tendsto (fun n : ℕ => ∑' i, c i * ((1 + e i t) / 2) ^ n * e i a) Filter.atTop
      (nhds (∑' i, (if e i t = 1 then c i else 0) * e i a)) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun i => ?_) (Filter.Eventually.of_forall fun n i => hb n a i)
    by_cases h : e i t = 1
    · simp [h]
    · have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_half_lt_one (hle i t) h)).const_mul (c i)).mul_const
        (e i a)
      simpa [h] using this
  simp only [hn] at hl
  exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

theorem charSeries_remove {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hne : ∀ i, i ≠ i₀ → ∃ a, e i a ≠ 1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, rfl, by simp, fun _ => le_rfl, hF⟩
  | insert j s hj ih =>
    obtain ⟨c', h1, h2, h3, h4⟩ := ih
    by_cases hji : j = i₀
    · refine ⟨c', h1, ?_, h3, h4⟩
      intro i hi hne
      rcases Finset.mem_insert.1 hi with h | h
      · exact absurd (h.trans hji) hne
      · exact h2 i h hne
    obtain ⟨t, ht⟩ := hne j hji
    refine ⟨fun i => if e i t = 1 then c' i else 0, ?_, ?_, ?_, ?_⟩
    · simp [h0, h1]
    · intro i hi hne
      rcases Finset.mem_insert.1 hi with h | h
      · subst h; simp [ht]
      · simp [h2 i h hne]
    · intro i
      by_cases h : e i t = 1
      · simpa [h] using h3 i
      · simp [h]
    · exact charSeries_restrict e c' hmul hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h3 hs) h4 t

theorem charSeries_coeff_eq_zero {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hne : ∀ i, i ≠ i₀ → ∃ a, e i a ≠ 1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) : c i₀ = 0 := by
  classical
  by_contra hc
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.2 hc
  have ht := tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖)
  have hev := (ht.eventually (gt_mem_nhds hpos)).and (Filter.eventually_ge_atTop ({i₀} : Finset I))
  obtain ⟨s, hs1, hs2⟩ := hev.exists
  have hi₀ : i₀ ∈ s := hs2 (Finset.mem_singleton_self _)
  obtain ⟨c', h1, h2, h3, h4⟩ := charSeries_remove e c i₀ hmul hle h0 hne hs hF s
  have hb : ∀ i, ‖c' i * e i 0‖ ≤ ‖c i‖ := by
    intro i
    rw [norm_mul]
    calc ‖c' i‖ * ‖e i 0‖ ≤ ‖c' i‖ * 1 := by gcongr; exact hle i 0
      _ ≤ ‖c i‖ := by rw [mul_one]; exact h3 i
  have hsum : Summable (fun i => c' i * e i 0) := Summable.of_norm_bounded hs hb
  have hsplit := hsum.sum_add_tsum_subtype_compl s
  rw [h4 0, Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi hne => by simp [h2 i hi hne]),
    h0, h1, mul_one] at hsplit
  have hle' : ‖∑' i : {x // x ∉ s}, c' i * e i 0‖ ≤ ∑' i : {x // x ∉ s}, ‖c i‖ :=
    tsum_of_norm_bounded (hs.subtype _).hasSum (fun i => hb i)
  rw [eq_neg_of_add_eq_zero_right hsplit, norm_neg] at hle'
  linarith

theorem theta_inj : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ Φ ∈ schA F κ, (∀ w, thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  intro F _ _ _ _ κ _ ψ hc h1 hF Φ hΦ hθ
  classical
  funext x
  have hnorm := (GlobalTheory.T.adelic_character_rational_dual F ψ hc h1 hF).1
  have hs := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).1 _ ((GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hc h1 hF).1 (x, 0) Φ hΦ)
  have key := charSeries_coeff_eq_zero (A := κ → AdeleRing (𝓞 F) F) (I := κ → F)
    (fun ξ y => ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ y))
    (fun ξ => Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + x)) 0
    (fun ξ a b => by simp only [dotProduct_add, AddChar.map_add_eq_mul]) (fun ξ a => (hnorm _).le)
    (fun a => by simp [dotProduct]) ?_ ?_ ?_
  · have e : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) + x) = x := by
      funext i; simp
    rw [e] at key
    exact key
  · intro ξ hξ
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
    have hi : ξ i ≠ 0 := hi
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨Pi.single i (algebraMap F (AdeleRing (𝓞 F) F) (ξ i)⁻¹ * a), ?_⟩
    simp only [dotProduct_single]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    simpa using ha
  · simpa [schr] using hs
  · intro y
    have h := hθ (x, y)
    simp only [thetaSum, schr, AddChar.map_add_eq_mul] at h
    have hne : ψ (⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ y)) ≠ 0 := by
      rw [← norm_ne_zero_iff, hnorm]; exact one_ne_zero
    apply mul_left_cancel₀ hne
    rw [← tsum_mul_left, mul_zero, ← h]
    exact tsum_congr fun ξ => by ring

end GlobalTheory.CompanionTheory.ThetaInj
