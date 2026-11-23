import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBoundsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimesPrincipalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBoundsStatement

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.NormPrimes

open Formalism.HermitianLattices.GL2PrimeSums

theorem err_le_rhoErr {CA c₃ Q B Y : ℝ} (hCA : 0 < CA) (hc : 0 < c₃) (hQ : 1 < Q) (hQB : Q ≤ B)
    (hY : 1 ≤ Y) :
    CA * (Real.exp (-c₃ * Real.log Y / Real.log Q) + Real.exp (-Real.sqrt (c₃ * Real.log Y / 2))) ≤
      rhoErr CA (min c₃ (Real.sqrt (c₃ / 2))) B Y := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlQ : 0 < Real.log Q := Real.log_pos hQ
  have hlQB : Real.log Q ≤ Real.log B := Real.log_le_log (by linarith) hQB
  have hm0 : 0 ≤ min c₃ (Real.sqrt (c₃ / 2)) := le_min hc.le (Real.sqrt_nonneg _)
  unfold rhoErr
  rw [mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCA.le)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCA.le)
  · rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div₀ (mul_nonneg hc.le hL) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
      hlQ hlQB
  · rw [neg_mul, neg_le_neg_iff, show c₃ * Real.log Y / 2 = c₃ / 2 * Real.log Y by ring,
      Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)

theorem exceptional_bounds {cS Q B β : ℝ} (hc : 0 < cS) (hQ : 4 ≤ Q) (hQB : Q ≤ B)
    (h1 : 1 - 1 / (8 * Real.log Q) < β) (h2 : cS / (Q ^ 2 * Real.log Q) ≤ 1 - β) :
    1 / 2 ≤ β ∧ β < 1 ∧ cS / (B ^ 2 * Real.log B) ≤ 1 - β := by
  have hl1 : 1 ≤ Real.log Q := by
    have h1 : Real.log 4 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hlQB : Real.log Q ≤ Real.log B := Real.log_le_log (by linarith) hQB
  have hQ0 : 0 < Q := by linarith
  have hp : 0 < Q ^ 2 * Real.log Q := mul_pos (by positivity) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have : 1 / (8 * Real.log Q) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · have := div_pos hc hp
    linarith
  · refine le_trans (div_le_div_of_nonneg_left hc.le hp ?_) h2
    exact mul_le_mul (pow_le_pow_left₀ hQ0.le hQB 2) hlQB (by linarith) (by positivity)

theorem normOne_of_generator {K : Type} [Field K] [NumberField K] {d M : ℕ} {ω : 𝓞 K}
    (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    NormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * ω := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  have h0 : 0 ≤ Algebra.norm ℤ π := by
    have : 0 ≤ (2 * (1 + (M : ℤ) * a) + M * b) ^ 2 + d * ((M : ℤ) * b) ^ 2 := by positivity
    linarith
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, Dvd.intro _ rfl, ⟨a, by ring⟩⟩
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg h0]
  linarith

theorem ncard_le_two_mul_card {α : Type} {T : Set α} (hT : T.Finite) (f : α → ℕ) (F : Finset ℕ)
    (hF : ∀ v ∈ T, f v ∈ F) (h2 : ∀ p ∈ F, {v ∈ T | f v = p}.ncard ≤ 2) :
    T.ncard ≤ 2 * F.card := by
  classical
  rw [Set.ncard_eq_toFinset_card T hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f) (fun v hv => hF v (by simpa using hv)) 2
    (fun p hp => ?_)
  refine le_trans (le_of_eq ?_) (h2 p hp)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem normPrimes_short_interval : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M → ∀ X h : ℝ, (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ C₀ ≤ X → h ≤ 1 → Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * (d : ℝ) * (M : ℝ) ^ 2) X ≤ h / 100 → (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) → c * h * (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d M X (X * (1 + h))).card : ℝ) := by
  rintro ⟨c₂, c₃, CA, cS, hc₂, hc₃, hCA, hcS, HT⟩
  have hcr : 0 < min c₃ (Real.sqrt (c₃ / 2)) := lt_min hc₃ (Real.sqrt_pos.2 (by positivity))
  obtain ⟨C₀, c, hC₀, hc, H⟩ := Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA _ cS hc₂ hCA hcr hcS
  refine ⟨C₀, CA, _, c / 2, by linarith, hCA, hcr, by positivity, ?_⟩
  intro d M hdp hd4 hd100 hM X h hX hh1 hρ hB7
  obtain ⟨K, _, _, ω, hK, h2, hD, -, hgen, hnorm⟩ :=
    GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hdp hd4
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  set 𝔮 : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with h𝔮
  have hq0 : 𝔮 ≠ ⊥ := by
    rw [h𝔮, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  have hNq : (Ideal.absNorm 𝔮 : ℝ) = (M : ℝ) ^ 2 := by
    rw [h𝔮, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
    push_cast; rfl
  have hDR : |(discr K : ℝ)| = d := by
    rw [hD]; push_cast; rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := one_le_pow₀ hMR
  obtain ⟨Q, β, θ, S, hQ1, hQ2, hθ, hβ, hS, hmain⟩ := HT K hK h2 𝔮 hq0
  rw [hDR] at hQ1 hQ2
  rw [hNq] at hQ2
  have hQB : Q ≤ B := hQ2
  have hQ4 : 4 ≤ Q := by linarith
  have hB4 : 4 ≤ B := by linarith
  obtain ⟨hfin, hfib, hdiv⟩ := GlobalTheory.T.prime_ideals_counting_bounds K hK h2
  obtain ⟨hG1, hG2, -⟩ := GlobalTheory.T.ray_class_number_bounds K 𝔮 hq0
  have hcl := GlobalTheory.classNumber_le_four_mul_abs_discr K h2
  rw [hDR] at hcl
  have hGB : (rayNo 𝔮 : ℝ) ≤ B := by
    have h1 : (rayNo 𝔮 : ℝ) ≤ (classNumber K : ℝ) * (Ideal.absNorm 𝔮 : ℝ) := by
      exact_mod_cast hG2
    rw [hNq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcl (by positivity))
  have hrfin : ∀ Y : ℝ, 1 ≤ Y → (rayPrimes 𝔮 Y).Finite := fun Y hY =>
    (hfin Y hY).1.subset (fun v hv => hv.2.1)
  let P₁ : ℝ → Set (HeightOneSpectrum (𝓞 K)) := fun Y =>
    {v ∈ rayPrimes 𝔮 Y | (Ideal.absNorm v.asIdeal).Prime}
  let P₂ : ℝ → Set (HeightOneSpectrum (𝓞 K)) := fun Y =>
    {v ∈ rayPrimes 𝔮 Y | ¬ (Ideal.absNorm v.asIdeal).Prime}
  have hsplit : ∀ Y : ℝ, 1 ≤ Y → (rayPrimes 𝔮 Y).ncard = (P₁ Y).ncard + (P₂ Y).ncard := by
    intro Y hY
    rw [← Set.ncard_union_eq ?_ ((hrfin Y hY).subset (fun v hv => hv.1))
      ((hrfin Y hY).subset (fun v hv => hv.1))]
    · congr 1
      ext v
      simp only [P₁, P₂, Set.mem_union, Set.mem_setOf_eq]
      tauto
    · exact Set.disjoint_left.2 (fun v hv hv' => hv'.2 hv.2)
  have hdfin : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite :=
    Ideal.finite_factors hq0
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow (by linarith) (by linarith)) hX
  have key := (H B (rayNo 𝔮) β θ (fun Y => (P₁ Y).ncard) (fun Y => (P₂ Y).ncard)
    (fun Y => ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard : ℝ)) hB4
    (by exact_mod_cast hG1) hGB (by rcases hθ with h | h <;> simp [h])
    (fun h0 => by
      obtain ⟨a, b⟩ := hβ (by omega)
      exact exceptional_bounds hcS hQ4 hQB a b)
    (fun Y hY => by
      have h1 : (P₂ Y).ncard ≤ {v : HeightOneSpectrum (𝓞 K) |
          (Ideal.absNorm v.asIdeal : ℝ) ≤ Y ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard :=
        Set.ncard_le_ncard (fun v hv => ⟨hv.1.2.1, hv.2⟩)
          ((hfin Y hY).1.subset (fun v hv => hv.1))
      have h2 : ((P₂ Y).ncard : ℝ) ≤ _ := Nat.cast_le.2 h1
      have := (hfin Y hY).2
      have := Real.sqrt_nonneg Y
      linarith)
    (fun Y => by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have h1 : {v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard ≤
          {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard :=
        Set.ncard_le_ncard (fun v hv => hS v hv.1) hdfin
      have h2 : ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard : ℝ) ≤ _ := Nat.cast_le.2 h1
      have h3 := hdiv 𝔮 hq0
      rw [hNq] at h3
      have h4 : Real.log (4 * (M : ℝ) ^ 2) ≤ Real.log B :=
        Real.log_le_log (by positivity) (by rw [hB]; nlinarith)
      linarith)
    (fun Y hY => by
      have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY
      have h1 := hmain Y (le_trans (Real.rpow_le_rpow (by linarith) hQB hc₂.le) hY)
      rw [hsplit Y hY1] at h1
      push_cast at h1
      have hE : 0 ≤ Emain θ β Y :=
        nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h1) (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_right
        (err_le_rhoErr hCA hc₃ (by linarith) hQB hY1) hE))
    X hX).2 h hh1 hρ hB7
  have hρ0 : 0 < rhoErr CA (min c₃ (Real.sqrt (c₃ / 2))) B X := by unfold rhoErr; positivity
  have hh0 : 0 < h := by linarith
  have hX' : 1 ≤ X * (1 + h) := by nlinarith
  have hP1 : (P₁ (X * (1 + h))).Finite := (hrfin _ hX').subset (fun v hv => hv.1)
  have hP0 : (P₁ X).Finite := (hrfin _ hX1).subset (fun v hv => hv.1)
  have hcount : (P₁ (X * (1 + h)) \ P₁ X).ncard ≤ 2 * (normPrimes d M X (X * (1 + h))).card := by
    refine ncard_le_two_mul_card (hP1.subset Set.diff_subset)
      (fun v => Ideal.absNorm v.asIdeal) _ ?_ ?_
    · rintro v ⟨⟨hv, hp⟩, hn⟩
      have hlt : X < (Ideal.absNorm v.asIdeal : ℝ) := by
        by_contra hle
        exact hn ⟨⟨hv.1, not_lt.1 hle, hv.2.2⟩, hp⟩
      obtain ⟨π, hπ1, hπ2⟩ := GlobalTheory.T.ray_primes_principal_generator K 𝔮 hq0 _ v hv
      have hN := normOne_of_generator hgen hnorm hπ2
      rw [← hπ1] at hN
      unfold normPrimes
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨(Nat.floor_lt (by linarith)).2 hlt, Nat.le_floor hv.2.1⟩, hp, hN⟩
    · intro p hp
      have hpp : p.Prime := by
        unfold normPrimes at hp
        simp only [Finset.mem_filter] at hp
        exact hp.2.1
      refine le_trans (Set.ncard_le_ncard (fun v hv => hv.2) ?_) (hfib p hpp)
      refine (hfin p (by exact_mod_cast hpp.one_lt.le)).1.subset (fun v hv => ?_)
      have : Ideal.absNorm v.asIdeal = p := hv
      simp [this]
  have hle : (P₁ (X * (1 + h))).ncard ≤ (P₁ (X * (1 + h)) \ P₁ X).ncard + (P₁ X).ncard :=
    Set.ncard_le_ncard_diff_add_ncard _ _ hP0
  have hR : ((P₁ (X * (1 + h))).ncard : ℝ) ≤
      2 * ((normPrimes d M X (X * (1 + h))).card : ℝ) + (P₁ X).ncard := by
    exact_mod_cast hle.trans (Nat.add_le_add_right hcount _)
  have e : c / 2 * h * B ^ (-6 : ℝ) * X / Real.log X
      = (c * h * B ^ (-6 : ℝ) * X / Real.log X) / 2 := by ring
  rw [e]
  linarith

end GlobalTheory.Mem.NormPrimes
