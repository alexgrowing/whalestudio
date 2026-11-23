import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower
import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
import Formalism.LogVandermondeBounds.LogVandermondeProofs.BlockDimensionIdentities

namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

theorem sharp_hecke_spectral_gap : SW_hecke_gap_sharp := by
  intro q _
  norm_num

theorem dimension_mass_joint_bound : DimensionMassJointBound := by
  intro f Dstar volY massr Isig dsig dimV hm hI hv h2 h3 hD
  rw [hD, h2]
  have hp : ∏ ρ ∈ range f, ((1 - 1 / 3 : ℝ) * dimV ρ) ≤ ∏ ρ ∈ range f, dsig ρ :=
    Finset.prod_le_prod (fun ρ hρ => mul_nonneg (by norm_num) (hv ρ (Finset.mem_range.1 hρ)))
      (fun ρ hρ => h3 ρ (Finset.mem_range.1 hρ))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hp
  have e : (1 - 1 / 3 : ℝ) = 2 / 3 := by norm_num
  rw [e] at hp
  calc (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ
      = massr * Isig * ((2 / 3 : ℝ) ^ f * ∏ ρ ∈ range f, dimV ρ) := by ring
    _ ≤ massr * Isig * ∏ ρ ∈ range f, dsig ρ := mul_le_mul_of_nonneg_left hp (mul_pos hm hI).le

private lemma triangular_numbers_half (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  have hY : k * (k + 1) / 2 = k * (k - 1) / 2 + k := by
    have e : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ n => rw [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  refine ⟨k * (k - 1) / 2, rfl, hY, ?_⟩
  have := half_add_half k
  rw [hY] at this
  linarith

private lemma odd_square_expansion (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring

private lemma exponent_square_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  rw [odd_square_expansion, show (k + 1) ^ 2 = k * k + 2 * k + 1 by ring, hA]
  generalize s * k = X
  generalize s * s = Y
  constructor <;> omega

private lemma card_general_linear_group (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [cardGeneralLinear F n, ← pow_add, half_add_half]

theorem local_index_formula : LocalColumnIndex := by
  intro F _ _ _ k m hm hme hF
  dsimp only
  have hg3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hg0 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2]
  obtain ⟨hb1, hb2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 k
  obtain ⟨hc1, hc2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 (k + 2 * s + 1)
  refine ⟨⟨_, hb1, hb2, ?_⟩, ⟨_, hc1, hc2, ?_⟩⟩
  · rw [cardGeneralLinear F k, div_eq_iff (pow_ne_zero _ hg0)]
    ring
  · rw [card_general_linear_group F, (exponent_square_identities k s A hA3).1, (exponent_square_identities k s A hA3).2, hA1]
    have hexp : (k + 2 * s + 1) * (k + 2 * s + 1) = (2 * (s * k) + s + 2 * (s * s)) + A +
        (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
      rw [← sq, odd_square_expansion, hA3]
      ring
    rw [hexp, pow_add, pow_add,
      div_eq_iff (mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hg0))]
    ring

private lemma prod_two_factor_split (f E : ℕ) (G : Fin 2 → ℝ) (t : Fin 2 → ℕ → ℝ) :
    ∏ i, ∏ ρ ∈ range f, G i ^ E * t i ρ =
      (G 0 * G 1) ^ (E * f) * ∏ i, ∏ ρ ∈ range f, t i ρ := by
  simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [mul_pow, pow_mul, pow_mul]

private lemma prod_half_to_one_bounds (f : ℕ) (t : Fin 2 → ℕ → ℝ) (h : ∀ i ρ, 1 / 2 ≤ t i ρ ∧ t i ρ ≤ 1) :
    ((2 : ℝ) ^ (2 * f))⁻¹ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ ∧ ∏ i, ∏ ρ ∈ range f, t i ρ ≤ 1 := by
  have h0 : ∀ i ρ, 0 ≤ t i ρ := fun i ρ => le_trans (by norm_num) (h i ρ).1
  constructor
  · calc ((2 : ℝ) ^ (2 * f))⁻¹ = ∏ i : Fin 2, ∏ ρ ∈ range f, (1 / 2 : ℝ) := by
          simp only [Finset.prod_const, Finset.card_range, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, one_div, inv_pow, mul_comm]
      _ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun ρ _ => by norm_num)
            (fun i _ => Finset.prod_le_prod (fun ρ _ => by norm_num) (fun ρ _ => (h i ρ).1))
  · exact Finset.prod_le_one (fun i _ => Finset.prod_nonneg fun ρ _ => h0 i ρ)
      (fun i _ => Finset.prod_le_one (fun ρ _ => h0 i ρ) (fun ρ _ => (h i ρ).2))

theorem index_ratio_bound : IndexRatioComparison := by
  intro f k m g₁ g₂ Ipi Isig θ θ' hm hme hg1 hg2 hθ
  dsimp only
  intro hIpi hIsig
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2] at hIsig
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  rw [(exponent_square_identities k s A hA3).2, prod_two_factor_split] at hIsig
  rw [hA2, prod_two_factor_split] at hIpi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hIpi hIsig
  obtain ⟨hPl, hPu⟩ := prod_half_to_one_bounds f θ (fun i ρ => ⟨(hθ i ρ).1, (hθ i ρ).2.1⟩)
  obtain ⟨hQl, hQu⟩ := prod_half_to_one_bounds f θ' (fun i ρ => ⟨(hθ i ρ).2.2.1, (hθ i ρ).2.2.2⟩)
  have hX0 : 0 < g₁ * g₂ := by nlinarith
  have hc : (0 : ℝ) < ((2 : ℝ) ^ (2 * f))⁻¹ := by positivity
  have hPpos : 0 < ∏ i, ∏ ρ ∈ range f, θ i ρ := lt_of_lt_of_le hc hPl
  have hN : (g₁ * g₂) ^ ((f : ℝ) * ((2 * s + 2 : ℕ) : ℝ) * (2 * (k : ℝ) + ((2 * s + 2 : ℕ) : ℝ) - 1) / 2) =
      (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hratio : Isig / Ipi = (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) *
      ((∏ i, ∏ ρ ∈ range f, θ' i ρ) / ∏ i, ∏ ρ ∈ range f, θ i ρ) := by
    rw [hIsig, hIpi]
    have e : (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) * f =
        (A + k) * f + (2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f := by ring
    rw [e, pow_add, mul_assoc, mul_div_mul_left _ _ (pow_pos hX0 _).ne', mul_div_assoc]
  rw [hN, hratio]
  have hXN : 0 ≤ (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) :=
    (pow_pos hX0 _).le
  have h22 : (2 : ℝ) ^ (2 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  constructor
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))⁻¹]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [le_div_iff₀ hPpos]
    nlinarith
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [div_le_iff₀ hPpos]
    nlinarith [mul_le_mul_of_nonneg_left hPl (by positivity : (0 : ℝ) ≤ 2 ^ (2 * f))]

private lemma card_orbits_mul_card_eq_card_of_free (G Y : Type) [Group G] [Fintype G] [Fintype Y] [MulAction G Y]
    (h : ∀ y : Y, MulAction.stabilizer G y = ⊥) :
    Nat.card (MulAction.orbitRel.Quotient G Y) * Fintype.card G = Fintype.card Y := by
  classical
  have hc : ∀ ω : MulAction.orbitRel.Quotient G Y,
      Fintype.card (MulAction.stabilizer G ω.out) = 1 := by
    intro ω
    rw [Fintype.card_eq_nat_card, h]
    exact Subgroup.card_bot
  rw [MulAction.card_eq_sum_card_group_div_card_stabilizer G Y, Nat.card_eq_fintype_card]
  simp only [hc, Nat.div_one, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem rank_count_bis : RankCountExact := by
  intro ι _ Γ _ _ Y _ _ hfree
  have hi : ∀ i, (Nat.card (MulAction.orbitRel.Quotient (Γ i) Y) : ℝ) =
      ((Fintype.card (Γ i) : ℝ))⁻¹ * Fintype.card Y := by
    intro i
    have h := card_orbits_mul_card_eq_card_of_free (Γ i) Y (hfree i)
    have hpos : (0 : ℝ) < Fintype.card (Γ i) := by exact_mod_cast Fintype.card_pos
    rw [eq_inv_mul_iff_mul_eq₀ hpos.ne', ← h]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_mul]

private lemma increments_sum_lower_bound (m : ℕ) (b : ℕ → ℝ) (h₀ : ℝ) (hb : ∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j)
    (a : ℕ) : ∀ d, a + d < m → (d : ℝ) * h₀ ≤ b (a + d) - b a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := hb (a + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

theorem least_noncompact_gap : LeastNoncompactGap := by
  intro k m v b h₀ hk hh hv hb0 hb i j hij hj hsg
  simp only [plusSign, ne_eq, decide_eq_decide] at hsg
  by_cases hi : i < k - 1
  · by_cases hj' : j < k - 1
    · exact absurd ⟨fun _ => Or.inl hj', fun _ => Or.inl hi⟩ hsg
    · have hodd : (j - (k - 1)) % 2 = 1 := by
        by_contra hc
        exact hsg ⟨fun _ => Or.inr (by omega), fun _ => Or.inl hi⟩
      simp only [rowPar, hi, hj', if_true, if_false]
      have hst := increments_sum_lower_bound m b h₀ hb 0 (j - (k - 1)) (by omega)
      simp only [zero_add] at hst
      have h1 : (1 : ℝ) ≤ ((j - (k - 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - (k - 1))
      have := hv i hi
      nlinarith [mul_le_mul_of_nonneg_right h1 hh]
  · have hj' : ¬ j < k - 1 := by omega
    simp only [rowPar, hi, hj', if_false]
    have hst := increments_sum_lower_bound m b h₀ hb (i - (k - 1)) (j - (k - 1) - (i - (k - 1))) (by omega)
    have e : i - (k - 1) + (j - (k - 1) - (i - (k - 1))) = j - (k - 1) := by omega
    rw [e] at hst
    have h1 : (1 : ℝ) ≤ ((j - (k - 1) - (i - (k - 1)) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ j - (k - 1) - (i - (k - 1)))
    nlinarith [mul_le_mul_of_nonneg_right h1 hh]

theorem rank_mul_pow_three_halves_le_fourth_power : RankMulPowThreeHalvesLeFourthPower := by
  intro f m k L hm hmf hk hL
  have hr3 : (3 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + m - 1)
  have hq1 : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m / 2)
  have hqf : 2 * ((m / 2 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast (by omega : 2 * (m / 2) ≤ f)
  have hf2 : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast (by omega : 2 ≤ f)
  set r : ℝ := ((k + m - 1 : ℕ) : ℝ)
  set q : ℝ := ((m / 2 : ℕ) : ℝ)
  have hpow : q ^ ((3 : ℝ) / 2) ≤ q ^ 2 := by
    rw [← Real.rpow_natCast q 2]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hq2 : q ^ 2 ≤ (f : ℝ) ^ 2 / 4 := by
    nlinarith [mul_le_mul hqf hqf (by linarith) (by linarith)]
  have hr3' : (27 : ℝ) ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hr3 3
    norm_num at this
    linarith
  have hf2' : (4 : ℝ) ≤ (f : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf2 2
    norm_num at this
    linarith
  have h30 : (30 : ℝ) ≤ r ^ 3 * (f : ℝ) ^ 2 := by
    have := mul_le_mul hr3' hf2' (by norm_num) (by linarith)
    linarith
  have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
  have hr0 : 0 ≤ r := by linarith
  have hrf : 0 ≤ r * (f : ℝ) ^ 2 := mul_nonneg hr0 (by positivity)
  calc 120 * r * q ^ ((3 : ℝ) / 2) ≤ 120 * r * q ^ 2 := mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ 120 * r * ((f : ℝ) ^ 2 / 4) := mul_le_mul_of_nonneg_left hq2 (by linarith)
    _ = (r * (f : ℝ) ^ 2) * 30 := by ring
    _ ≤ (r * (f : ℝ) ^ 2) * (r ^ 3 * (f : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h30 hrf
    _ = (r * f) ^ 4 * 1 := by ring
    _ ≤ (r * f) ^ 4 * L ^ 4 := mul_le_mul_of_nonneg_left hL4 (by positivity)
    _ = (r * f * L) ^ 4 := by ring

theorem hypotheses_of_third_theorem : RankThresholdInequalityEventually := by
  intro ε C C₀ hε hC hC₀
  set a0 := 9 * C / 16 * Real.log 2 with ha0
  set a1 := 9 * C * C₀ / (16 * ε) with ha1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha0n : 0 ≤ a0 := mul_nonneg (by positivity) hlog2
  have ha1n : 0 ≤ a1 := by positivity
  refine ⟨max 1 ((a0 + a1 + 1) ^ ε⁻¹), ?_⟩
  intro x hx f m k hm hme hmf hmk hkx
  dsimp only
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hy : a0 + a1 + 1 ≤ x ^ ε := by
    have h1 : (a0 + a1 + 1) ^ ε⁻¹ ≤ x := le_trans (le_max_right _ _) hx
    calc a0 + a1 + 1 = ((a0 + a1 + 1) ^ ε⁻¹) ^ ε :=
          (Real.rpow_inv_rpow (by positivity) hε.ne').symm
      _ ≤ x ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have eq1 : (2 * t + 2) / 2 = t + 1 := by omega
  have eq2 : k + (t + 1) - 1 = k + t := by omega
  have eq3 : k + (2 * t + 2) - 1 = k + 2 * t + 1 := by omega
  rw [eq1, eq2, eq3]
  have hR3 : (3 : ℝ) ≤ ((k + 2 * t + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 2 * t + 1)
  refine ⟨?_, by omega, by omega, ?_⟩
  · have := Real.add_one_le_exp ((k + 2 * t + 1 : ℕ) : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num),
      show ((1 : ℝ) / 3)⁻¹ = 3 by norm_num]
    linarith
  · rw [Nat.cast_mul]
    have hRk : ((k + 2 * t + 1 : ℕ) : ℝ) ≤ 2 * x ^ C₀ := by
      have : ((k + 2 * t + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        exact_mod_cast (by omega : k + 2 * t + 1 ≤ 2 * k)
      linarith
    have h2 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0.le hε
    set R : ℝ := ((k + 2 * t + 1 : ℕ) : ℝ) with hR
    set Q : ℝ := ((t + 1 : ℕ) : ℝ) with hQ
    set P : ℝ := ((k + t : ℕ) : ℝ) with hP
    set y := x ^ ε with hydef
    have hQ1 : 1 ≤ Q := by rw [hQ]; exact_mod_cast (by omega : 1 ≤ t + 1)
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    have hPR : P ≤ R := by rw [hP, hR]; exact_mod_cast (by omega : k + t ≤ k + 2 * t + 1)
    have hQf : 2 * Q ≤ f := by rw [hQ]; exact_mod_cast (by omega : 2 * (t + 1) ≤ f)
    have hy1 : 1 ≤ y := by linarith
    have hy0 : 0 ≤ y := by linarith
    have hlogR : Real.log R ≤ Real.log 2 + C₀ * (y / ε) := by
      have h1 : Real.log R ≤ Real.log (2 * x ^ C₀) := Real.log_le_log (by linarith) hRk
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h1
      nlinarith [mul_le_mul_of_nonneg_left h2 hC₀]
    have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    have hkey : 9 * C / 16 * (Real.log 2 + C₀ * (y / ε)) ≤ y ^ 4 := by
      have e : 9 * C / 16 * (Real.log 2 + C₀ * (y / ε)) = a0 + a1 * y := by
        rw [ha0, ha1]
        field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hy hy0, pow_le_pow_right₀ hy1 (by norm_num : 2 ≤ 4)]
    have hQ4 : Q ^ 4 ≤ (f : ℝ) ^ 4 / 16 := by
      have := pow_le_pow_left₀ (by linarith) hQf 4
      nlinarith
    have hPR3 : P ^ 3 * R ≤ R ^ 4 := by
      have := pow_le_pow_left₀ hP0 hPR 3
      nlinarith
    have hA := mul_le_mul hQ4 hPR3 (mul_nonneg (pow_nonneg hP0 3) (by linarith)) (by positivity)
    have hB := mul_le_mul_of_nonneg_left hA (mul_nonneg (by linarith : (0 : ℝ) ≤ 9 * C) hlog0)
    have hF : 0 ≤ (f : ℝ) ^ 4 * R ^ 4 := mul_nonneg (by positivity) (pow_nonneg (by linarith) 4)
    calc C * Q * (P * Q) ^ 3 * R * Real.log R / (1 / 3) ^ 2
        = 9 * C * Real.log R * (Q ^ 4 * (P ^ 3 * R)) := by ring
      _ ≤ 9 * C * Real.log R * ((f : ℝ) ^ 4 / 16 * R ^ 4) := hB
      _ = ((f : ℝ) ^ 4 * R ^ 4) * (9 * C / 16 * Real.log R) := by ring
      _ ≤ ((f : ℝ) ^ 4 * R ^ 4) * (9 * C / 16 * (Real.log 2 + C₀ * (y / ε))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogR (by linarith)) hF
      _ ≤ ((f : ℝ) ^ 4 * R ^ 4) * y ^ 4 := mul_le_mul_of_nonneg_left hkey hF
      _ = (R * f * y) ^ 4 := by ring

end Formalism.HermitianLattices.GenusMassVolumes
