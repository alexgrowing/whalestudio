import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem jetBd_log_le_pt (g n' i : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hn : 1 ≤ n') (hi : i ≤ n') :
    Real.log (jetBd g (4 * n') i ρ) ≤ (i : ℝ) / 2 * Real.log (Real.exp 1 * (4 * n') * n') +
      (1 / 2 + Real.log (Nat.factorial g) / 2 + (g / 2) * Real.log (4 * n') + g * (Real.log (4 / Real.pi) / 2)) +
      (g / 2) * Real.log (1 + (ρ ^ 2)⁻¹) := by
  have hpi := Real.pi_pos
  have hn0 : (1 : ℝ) ≤ n' := by exact_mod_cast hn
  set a : ℝ := (√Real.pi / 2 * ρ)⁻¹ with ha
  set b : ℝ := √((4 * n' : ℕ) : ℝ) with hb
  have ha0 : 0 < a := by positivity
  have hb1 : 1 ≤ b := by rw [hb, Real.one_le_sqrt]; push_cast; linarith
  set c := max a 1 with hc
  have hc1 : 1 ≤ c := le_max_right _ _
  have hA : Real.log (√(Real.exp 1 * ((4 * n' : ℕ) : ℝ) * i) ^ i) ≤
      (i : ℝ) / 2 * Real.log (Real.exp 1 * (4 * n') * n') := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp
    · rw [Real.log_pow, Real.log_sqrt (by positivity)]
      have hi' : (1:ℝ) ≤ i := by exact_mod_cast hpos
      have hi2 : (i:ℝ) ≤ n' := by exact_mod_cast hi
      have : Real.log (Real.exp 1 * ((4 * n' : ℕ) : ℝ) * i) ≤ Real.log (Real.exp 1 * (4 * n') * n') := by
        apply Real.log_le_log (by positivity)
        push_cast
        gcongr
      nlinarith
  have hB : Real.log (√(Real.exp 1 * (Nat.factorial g : ℝ))) = 1 / 2 + Real.log (Nat.factorial g) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]; ring
  have hlb : Real.log b = Real.log (4 * n') / 2 := by
    rw [hb, Real.log_sqrt (by positivity)]; push_cast; ring
  have ha2 : a ^ 2 = 4 / Real.pi * (ρ ^ 2)⁻¹ := by
    rw [ha, inv_pow, mul_pow, div_pow, Real.sq_sqrt hpi.le]; field_simp; ring
  have hc2 : c ^ 2 ≤ 4 / Real.pi * (1 + (ρ ^ 2)⁻¹) := by
    have h4 : 1 ≤ 4 / Real.pi := by rw [le_div_iff₀ hpi]; linarith [Real.pi_le_four]
    have hr : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
    rcases le_total a 1 with h | h
    · rw [hc, max_eq_right h]; nlinarith
    · rw [hc, max_eq_left h, ha2]; nlinarith
  have hlc : Real.log c ≤ (Real.log (4 / Real.pi) + Real.log (1 + (ρ ^ 2)⁻¹)) / 2 := by
    have h1 : Real.log (c ^ 2) ≤ Real.log (4 / Real.pi * (1 + (ρ ^ 2)⁻¹)) :=
      Real.log_le_log (by positivity) hc2
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at h1
    push_cast at h1; linarith
  have hMle : max (a ^ g) (b ^ g) ≤ (b * c) ^ g := by
    have hb0 : 0 ≤ b := by linarith
    apply max_le
    · apply pow_le_pow_left₀ ha0.le
      calc a ≤ c := le_max_left _ _
        _ ≤ b * c := le_mul_of_one_le_left (by linarith) hb1
    · exact pow_le_pow_left₀ hb0 (le_mul_of_one_le_right hb0 hc1) g
  have hM0 : 0 < max (a ^ g) (b ^ g) := lt_max_of_lt_left (pow_pos ha0 g)
  have hM : Real.log (max (a ^ g) (b ^ g)) ≤
      (g / 2) * Real.log (4 * n') + g * (Real.log (4 / Real.pi) / 2) + (g / 2) * Real.log (1 + (ρ ^ 2)⁻¹) := by
    have h1 := Real.log_le_log hM0 hMle
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), hlb] at h1
    have hg : (0 : ℝ) ≤ g := by positivity
    have h2 : (g : ℝ) * Real.log c ≤ g * ((Real.log (4 / Real.pi) + Real.log (1 + (ρ ^ 2)⁻¹)) / 2) :=
      mul_le_mul_of_nonneg_left hlc hg
    nlinarith
  have hpos1 : 0 < √(Real.exp 1 * ((4 * n' : ℕ) : ℝ) * i) ^ i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp
    · have : (0:ℝ) < i := by exact_mod_cast hpos
      positivity
  unfold jetBd
  rw [Real.log_mul (by positivity) hM0.ne', Real.log_mul hpos1.ne' (by positivity), hB]
  linarith

end GlobalTheory

namespace GlobalTheory

theorem jetBd_log_mean_le : ∀ (g : ℕ) (K : Type) [Field K] [NumberField K] (ρ : (K →+* ℂ) → ℝ) (H : ℝ) (n' i : ℕ), 0 ≤ H → (∀ σ, 0 < ρ σ) → (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤ 14 * (1 + H + Real.log (Nat.factorial g)) → 1 ≤ n' → i ≤ n' → (∑ σ, Real.log (jetBd g (4 * n') i (ρ σ))) / (Module.finrank ℚ K : ℝ) ≤ (i : ℝ) / 2 * Real.log (Real.exp 1 * (4 * n') * n') + (1 / 2 + Real.log (Nat.factorial g) / 2 + (g / 2) * Real.log (4 * n') + g * ((Real.log (4 / Real.pi) + Real.log (15 + 14 * Real.log (Nat.factorial g))) / 2) + (g / 2) * Real.log (2 + H)) := by
  intro g K _ _ ρ H n' i hH hρ hmean hn hi
  have hcardN : Fintype.card (K →+* ℂ) = Module.finrank ℚ K := NumberField.Embeddings.card K ℂ
  have hNpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  haveI : Nonempty (K →+* ℂ) := Fintype.card_pos_iff.mp (hcardN ▸ hNpos)
  set N : ℝ := (Module.finrank ℚ K : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hNpos
  set L : ℝ := Real.log (Nat.factorial g) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero g))
  set C : ℝ := (i : ℝ) / 2 * Real.log (Real.exp 1 * (4 * n') * n') +
      (1 / 2 + L / 2 + (g / 2) * Real.log (4 * n') + g * (Real.log (4 / Real.pi) / 2)) with hC
  set t : (K →+* ℂ) → ℝ := fun σ => (ρ σ ^ 2)⁻¹ with ht
  have ht0 : ∀ σ, 0 ≤ t σ := fun σ => by simp only [ht]; positivity
  have hpt : ∀ σ, Real.log (jetBd g (4 * n') i (ρ σ)) ≤ C + (g / 2) * Real.log (1 + t σ) :=
    fun σ => jetBd_log_le_pt g n' i (ρ σ) (hρ σ) hn hi
  have hsum : ∑ σ, Real.log (jetBd g (4 * n') i (ρ σ)) ≤ N * C + (g / 2) * ∑ σ, Real.log (1 + t σ) := by
    refine (Finset.sum_le_sum fun σ _ => hpt σ).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hcardN]
  have hjen := ReciprocityTheory.GeometryOfNumbersTheory.wma_sum_log_le t ht0
  rw [hcardN] at hjen
  have hlog : Real.log (1 + (∑ σ, t σ) / N) ≤ Real.log (15 + 14 * L) + Real.log (2 + H) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    have h0 : 0 ≤ (∑ σ, t σ) / N := div_nonneg (Finset.sum_nonneg fun σ _ => ht0 σ) hN.le
    apply Real.log_le_log (by positivity)
    have : (∑ σ, t σ) / N ≤ 14 * (1 + H + L) := hmean
    nlinarith
  have hg : (0 : ℝ) ≤ g / 2 := by positivity
  have h3 : (g / 2 : ℝ) * ∑ σ, Real.log (1 + t σ) ≤ (g / 2) * (N * (Real.log (15 + 14 * L) + Real.log (2 + H))) := by
    apply mul_le_mul_of_nonneg_left _ hg
    exact hjen.trans (mul_le_mul_of_nonneg_left hlog hN.le)
  rw [div_le_iff₀ hN]
  have h4 := hsum.trans (add_le_add le_rfl h3)
  refine h4.trans (le_of_eq ?_)
  rw [hC]; ring

end GlobalTheory
