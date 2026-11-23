import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat

open Finset Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.Mem.An

theorem tzRat_class_bound (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧
      ∀ (M b : ℕ) (B : ℝ), 3 ≤ M → M % 4 ≠ 2 → Nat.Coprime b M → (M : ℝ) ≤ B →
        ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
          (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) ∧
          ∀ Y : ℝ, B ^ C₀ ≤ Y →
            |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
              - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y := by
  obtain ⟨c₂, c₃, CA, cS, h2, h3, hA, hS, H⟩ := h
  have hs3 : 0 < Real.sqrt c₃ := Real.sqrt_pos.2 h3
  refine ⟨c₂, CA, min c₃ (Real.sqrt c₃), cS, h2, hA, lt_min h3 hs3, hS, ?_⟩
  intro M b B hM hM4 hb hMB
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨-, HS, HC⟩ := H M hM hM4
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlM : 1 / 4 ≤ Real.log M := by
    have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  have hlMB : Real.log M ≤ Real.log B := Real.log_le_log hM0 hMB

  have key : ∀ (θ : ℤ) (β : ℝ),
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ M, IsExcRat χ β ∧ χ (b : ZMod M) = (θ : ℂ)) →
      ∀ Y : ℝ, B ^ c₂ ≤ Y →
        |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
          - Emain θ β Y| ≤ rhoErr CA (min c₃ (Real.sqrt c₃)) B Y * Emain θ β Y := by
    intro θ β hθ Y hY
    have hMY : (M : ℝ) ^ c₂ ≤ Y := le_trans (Real.rpow_le_rpow hM0.le hMB h2.le) hY
    have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) h2.le) hMY
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hq := HC b θ β hb hθ Y hMY
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log M) +
        Real.exp (-Real.sqrt (c₃ * Real.log Y))) := by positivity
    have hE : 0 ≤ Emain θ β Y := by
      have := le_trans (abs_nonneg _) hq
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    refine le_trans hq (mul_le_mul_of_nonneg_right ?_ hE)
    unfold rhoErr
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hA.le
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      have hm0 : 0 ≤ min c₃ (Real.sqrt c₃) := (lt_min h3 hs3).le
      calc min c₃ (Real.sqrt c₃) * Real.log Y / Real.log B
          ≤ min c₃ (Real.sqrt c₃) * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hlMB
        _ ≤ c₃ * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hL) (by linarith)
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_le_neg_iff, Real.sqrt_mul h3.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
  by_cases hex : ∃ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExcRat χ β
  · obtain ⟨χ, β, hχ⟩ := hex
    have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
    have hsq : χ (b : ZMod M) ^ 2 = 1 := by
      have h1 : (χ ^ 2) (b : ZMod M) = 1 := by
        rw [hχ.1]; exact MulChar.one_apply hu
      rwa [MulChar.pow_apply' χ (by norm_num)] at h1
    have hβ : 1 / 2 ≤ β ∧ β < 1 ∧ cS / (B ^ 2 * Real.log B) ≤ 1 - β := by
      refine ⟨?_, hχ.2.2.1, le_trans ?_ (HS χ β hχ)⟩
      · have h1 := hχ.2.1
        have h2 : 1 / (8 * Real.log M) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
      · have hl0 : 0 < Real.log M := by linarith
        apply div_le_div_of_nonneg_left hS.le (by positivity)
        have hB0 : 0 < B := by linarith
        gcongr
    rcases sq_eq_one_iff.1 hsq with h1 | h1
    · exact ⟨1, β, by simp, fun _ => hβ, key 1 β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
    · exact ⟨-1, β, by simp, fun _ => hβ, key (-1) β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
  · push_neg at hex
    exact ⟨0, 0, by simp, fun h => absurd rfl h, key 0 0 (Or.inl ⟨rfl, hex⟩)⟩

theorem card_primes_mod_half (n a N : ℕ) (hn : Odd n) (ha : Nat.Coprime a (2 * n)) :
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ∧
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card + 1 := by
  constructor
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.of_mul_left 2⟩
  · refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le 2 _)
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases h2 : p = 2
    · exact Or.inl h2
    · right
      refine ⟨hp.1, hp.2.1, ?_⟩
      have hc : Nat.Coprime 2 n := (Nat.coprime_two_left).2 hn
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
      refine ⟨?_, hp.2.2⟩
      have hpo : Odd p := hp.2.1.odd_of_ne_two h2
      have hao : Odd a := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right ha)
      unfold Nat.ModEq
      rw [Nat.odd_iff.1 hpo, Nat.odd_iff.1 hao]

theorem tzRat_ratClass (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions C₀ Cr cr cb := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_class_bound h
  refine ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, ?_⟩
  intro m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 1 ≤ 3 * Real.log (4 * (m : ℝ)) := by
    have h1 : Real.log 2 ≤ Real.log (4 * (m : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  by_cases h4 : m % 4 = 2
  · obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    have hn : Odd n := Nat.odd_iff.2 (by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨θ, β, hθ, hβ, hE⟩ := H n a (4 * ((2 * n : ℕ) : ℝ)) (by omega) (by omega)
      (Nat.Coprime.coprime_mul_left_right ha) (by push_cast; linarith)
    refine ⟨θ, β, fun Y => (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card : ℝ) -
      (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card : ℝ), hθ, hβ, ?_, ?_⟩
    · intro Y
      obtain ⟨k1, k2⟩ := card_primes_mod_half n a ⌊Y⌋₊ hn ha
      have k1' := (Nat.cast_le (α := ℝ)).2 k1
      have k2' := (Nat.cast_le (α := ℝ)).2 k2
      rw [Nat.cast_add, Nat.cast_one] at k2'
      constructor <;> linarith
    · intro Y hY
      rw [Nat.totient_two_mul_of_odd hn, add_sub_cancel]
      exact hE Y hY
  · obtain ⟨θ, β, hθ, hβ, hE⟩ := H m a (4 * (m : ℝ)) hm h4 ha (by linarith)
    refine ⟨θ, β, fun _ => 0, hθ, hβ, fun _ => ⟨le_rfl, by linarith⟩, ?_⟩
    intro Y hY
    rw [add_zero]
    exact hE Y hY

theorem primesAPInterval_of_tzRat (h : TZRat) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ PrimesAPInterval C₀ Cr cr c := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_ratClass h
  obtain ⟨C₀', c, hC, hc, H'⟩ :=
    Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound C₀ Cr cr cb h0 h1 h2 h3 H
  exact ⟨C₀', Cr, cr, c, hC, h1, h2, hc, H'⟩

end GlobalTheory.Mem.An
