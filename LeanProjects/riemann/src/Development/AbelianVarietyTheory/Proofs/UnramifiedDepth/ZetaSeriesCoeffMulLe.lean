import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateFormStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightedOrderGePrimePowOfSumPurePowersAddStatement
open ReciprocityTheory.PGsh

namespace GlobalTheory

section Ord

open MvPowerSeries

variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)

theorem zetaSeries_ordGe_mono {g : MvPowerSeries (Fin M) C} {r s : ℝ} (h : OrdGe v ρ g r)
    (hsr : s ≤ r) : OrdGe v ρ g s :=
  fun α => le_trans (WithTop.coe_le_coe.2 (by linarith)) (h α)

theorem zetaSeries_ordGe_one : OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0 := by
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem zetaSeries_ordGe_mul {f g : MvPowerSeries (Fin M) C} {r s : ℝ} (hf : OrdGe v ρ f r)
    (hg : OrdGe v ρ g s) : OrdGe v ρ (f * g) (r + s) := by
  intro α
  rw [coeff_mul]
  apply v.map_le_sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [v.map_mul]
  have e : r + s - ∑ m, ρ m * (α m : ℝ) =
      (r - ∑ m, ρ m * (x.1 m : ℝ)) + (s - ∑ m, ρ m * (x.2 m : ℝ)) := by
    rw [← hx]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hf _) (hg _)

theorem zetaSeries_ordGe_pow {f : MvPowerSeries (Fin M) C} {r : ℝ} (hf : OrdGe v ρ f r) (n : ℕ) :
    OrdGe v ρ (f ^ n) (n * r) := by
  induction n with
  | zero => simpa using zetaSeries_ordGe_one v ρ
  | succ n ih =>
    rw [pow_succ]
    exact zetaSeries_ordGe_mono v ρ (zetaSeries_ordGe_mul v ρ ih hf) (by push_cast; linarith)

theorem zetaSeries_coeff_mul_le {c : C} {L : ℝ} (hc : ((L : ℝ) : WithTop ℝ) ≤ v c)
    {g : MvPowerSeries (Fin M) C} {s : ℝ} (hg : OrdGe v ρ g s) (α : Fin M →₀ ℕ) :
    (((L + s - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (c * coeff α g) := by
  rw [v.map_mul, show L + s - ∑ m, ρ m * (α m : ℝ) = L + (s - ∑ m, ρ m * (α m : ℝ)) by ring,
    WithTop.coe_add]
  exact add_le_add hc (hg α)

end Ord

theorem zetaSeries_ordGe_pure {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ}
    (N : ℕ) (r w : ℝ) (a : Fin M → C) (ha : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r)
      (∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) w := by
  classical
  intro α
  rw [map_sum]
  apply v.map_le_sum
  intro j _
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  split_ifs with h
  · subst h
    have : ∑ m, r * ((Finsupp.single j N : Fin M →₀ ℕ) m : ℝ) = r * N := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro m _ hm
        simp [Finsupp.single_apply, Ne.symm hm]
      · simp
    rw [this, mul_one]
    exact ha j
  · simp

theorem zetaSeries_geom (q : ℝ) (n s : ℕ) (hq : (n : ℝ) = q) :
    (q - 1) * ((∑ u ∈ Finset.range s, n ^ u : ℕ) : ℝ) = q ^ s - 1 := by
  push_cast
  rw [hq, mul_comm]
  exact geom_sum_mul q s

theorem zetaSeries_v_inv_pow {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (x : C)
    (hx : v x = 1) (n : ℕ) : v ((x ^ n)⁻¹) = ((-(n : ℝ) : ℝ) : WithTop ℝ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at hx
    exact absurd hx (by simp)
  have h1 : v (x ^ n) = ((n : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, hx, ← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  have h2 : v (x ^ n) + v ((x ^ n)⁻¹) = 0 := by
    rw [← v.map_mul, mul_inv_cancel₀ (pow_ne_zero _ hx0), v.map_one]
  rw [h1] at h2
  cases hv : v ((x ^ n)⁻¹) with
  | top => rw [hv] at h2; simp at h2
  | coe r =>
    rw [hv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h2
    congr 1
    linarith

theorem zetaSeries_main_term : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) → ∀ (d' : ℕ) (be : Fin d → ℕ → Fin d' → C) (b : Fin d'), (∀ c, be c 0 b = 0) → (∀ c (n : ℕ), ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n b)) →
    (∀ c ∈ good, ∀ n : ℕ, 2 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n b)) → (∀ s < s₀, ∀ c ∈ Gs s, be c 1 b = 0) →
    ∀ ζ : MvPowerSeries (Fin M) C, (∀ α, MvPowerSeries.coeff α ζ = -∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ c, be c n b * MvPowerSeries.coeff α (t c ^ (l ^ n))) →
    OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (ζ - ∑ j, MvPowerSeries.C (R := C) (((l : C) ^ (1 + l * (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u)))⁻¹ * ((-1) ^ (s₀ + 1) * ∑ c ∈ Gs s₀, π s₀ c j ^ l * ((l : C) * be c 1 b))) *
      (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (l ^ (2 * s₀ + 1))) 0) := by
  intro C _ _ v l hl hv h3 d M s₀ good Gs al π t hG hdisj hal0 hal hgood hal2 hπ0 hπ0' hπ ht0 ht
    d' be b hbe0 hbe hbeg hbe1 ζ hζ
  classical
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.chainLemma_multivariatePowerSeries_coordinate_form C v l hl hv h3 d M s₀ good Gs al π t hG hdisj hal0 hal hgood
    hal2 hπ0 hπ0' hπ ht0 ht
  have hl3 : (3 : ℝ) ≤ l := by exact_mod_cast h3
  have hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  set ρ : ℝ := 1 / ((l : ℝ) ^ 2 - 1) with hρ
  have hρq : ρ * ((l : ℝ) ^ 2 - 1) = 1 := by rw [hρ]; field_simp
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set σ : ℝ := 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hl0 : (l : C) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hπint : ∀ s e j, 0 ≤ v (π s e j) := by
    intro s
    induction s with
    | zero => exact hπ0
    | succ s ih =>
      intro e j
      rw [hπ]
      apply v.map_le_sum
      intro c hc
      rw [v.map_mul, v.map_mul, v.map_pow, hv]
      have h1 := (hgood c (hG s c hc)).2 2 e (by norm_num)
      have h2 : (0 : WithTop ℝ) ≤ 1 + v (al c 2 e) := by
        refine le_trans (le_of_eq ?_) (add_le_add le_rfl h1)
        rw [← WithTop.coe_one, ← WithTop.coe_add, ← WithTop.coe_zero]
        congr 1; push_cast; ring
      exact add_nonneg h2 (nsmul_nonneg (ih c j) _)
  have ha : ∀ s c j, ((ρ - (ρ + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
      v ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) := by
    intro s c j
    have hm : v ((-1 : C) ^ s) = 0 := by rw [v.map_pow, v.map_neg, v.map_one, smul_zero]
    rw [v.map_mul, v.map_mul, hm, zero_add, zetaSeries_v_inv_pow v _ hv]
    refine le_trans ?_ (le_add_of_nonneg_right (hπint s c j))
    rw [WithTop.coe_le_coe]
    have hg := zetaSeries_geom ((l : ℝ) ^ 2) (l ^ 2) s (by push_cast; ring)
    set e : ℝ := ((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ)
    have hQ : (((l ^ 2) ^ s : ℕ) : ℝ) = ((l : ℝ) ^ 2) ^ s := by push_cast; ring
    rw [hQ]
    have hQ0 : 0 ≤ σ * ((l : ℝ) ^ 2) ^ s := by positivity
    have : e = ρ * (((l : ℝ) ^ 2) ^ s - 1) := by
      rw [← hg, ← mul_assoc, hρq, one_mul]
    rw [this]; nlinarith
  have htG : ∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => ρ + σ) (t c) ρ := by
    intro s hs c hc
    have h1 := zetaSeries_ordGe_mono v _ (hc1 s hs c hc) (show ρ ≤ 1 + ρ by linarith)
    have h2 := zetaSeries_ordGe_pure v ((l ^ 2) ^ s) (ρ + σ) ρ _ (ha s c)
    intro α
    have := le_trans (le_min (h1 α) (h2 α)) (v.map_add _ _)
    rwa [← map_add, sub_add_cancel] at this

  set A : Fin d → Fin M → C := fun c j =>
    (-1) ^ s₀ * ((l : C) ^ (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u))⁻¹ * π s₀ c j with hA
  set P : Fin d → MvPowerSeries (Fin M) C := fun c =>
    ∑ j, MvPowerSeries.C (R := C) (A c j ^ (l ^ 1)) *
      (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s₀ * l ^ 1) with hP
  intro α
  have hterm : ∀ (n : ℕ) c, ((0 - ∑ m, (ρ + σ) * (α m : ℝ) : ℝ) : WithTop ℝ) ≤
      v (be c n b * MvPowerSeries.coeff α
        (t c ^ (l ^ n) - if n = 1 ∧ c ∈ Gs s₀ then P c else 0)) := by
    intro n c
    split_ifs with h
    · obtain ⟨rfl, hc⟩ := h
      have hf := GlobalTheory.T.weightedOrderGe_prime_pow_of_sum_pure_powers_add C v l hl hv M ((l ^ 2) ^ s₀) 1 (ρ + σ) ρ (1 + ρ) (A c) _
        (by linarith) (ha s₀ c) (hc1 s₀ le_rfl c hc)
      rw [add_sub_cancel] at hf
      refine le_trans ?_ (zetaSeries_coeff_mul_le v _ (hbe c 1) hf α)
      rw [WithTop.coe_le_coe]
      have : 1 ≤ min (1 + (l : ℝ) ^ 1 * ρ) ((l : ℝ) ^ 1 * (1 + ρ)) := by
        apply le_min <;> nlinarith
      push_cast
      linarith
    · rw [sub_zero]
      by_cases hc : ∃ s ≤ s₀, c ∈ Gs s
      · obtain ⟨s, hs, hc⟩ := hc
        rcases Nat.lt_or_ge n 2 with hn | hn
        · have : be c n b = 0 := by
            interval_cases n
            · exact hbe0 c
            · rcases hs.lt_or_eq with hs | rfl
              · exact hbe1 s hs c hc
              · exact absurd ⟨rfl, hc⟩ h
          simp [this]
        · refine le_trans ?_ (zetaSeries_coeff_mul_le v _ (hbeg c (hG s c hc) n hn)
            (zetaSeries_ordGe_pow v _ (htG s hs c hc) (l ^ n)) α)
          rw [WithTop.coe_le_coe]
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
          have h1 : m + 1 ≤ l ^ m := Nat.lt_pow_self hl.one_lt
          have h2 : (m : ℝ) + 1 ≤ (l : ℝ) ^ m := by exact_mod_cast h1
          have h4 : (m : ℝ) + 1 ≤ (l : ℝ) ^ (2 + m) * ρ := by
            have : (l : ℝ) ^ (2 + m) * ρ = (l : ℝ) ^ m * (1 + ρ) := by
              rw [pow_add]; linear_combination (l : ℝ) ^ m * hρq
            rw [this]
            have : 0 ≤ (l : ℝ) ^ m * ρ := by positivity
            linarith
          push_cast
          linarith
      · push_neg at hc
        refine le_trans ?_ (zetaSeries_coeff_mul_le v _ (hbe c n)
            (zetaSeries_ordGe_pow v _ (hc2 c hc) (l ^ n)) α)
        rw [WithTop.coe_le_coe]
        have h1 : n ≤ l ^ n := (Nat.lt_pow_self hl.one_lt).le
        have h2 : (n : ℝ) ≤ (l : ℝ) ^ n := by exact_mod_cast h1
        have : 0 ≤ (l : ℝ) ^ n * ρ := by positivity
        push_cast
        linarith
  have hexp : (l ^ 2) ^ s₀ * l ^ 1 = l ^ (2 * s₀ + 1) := by rw [← pow_mul, ← pow_add]
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hmain : MvPowerSeries.coeff α (∑ j, MvPowerSeries.C (R := C)
      (((l : C) ^ (1 + l * (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u)))⁻¹ *
        ((-1) ^ (s₀ + 1) * ∑ c ∈ Gs s₀, π s₀ c j ^ l * ((l : C) * be c 1 b))) *
      (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (l ^ (2 * s₀ + 1))) =
      -∑ c ∈ Gs s₀, be c 1 b * MvPowerSeries.coeff α (P c) := by
    simp only [hP, map_sum, MvPowerSeries.coeff_C_mul, hexp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    simp only [hA, pow_one, mul_pow]
    have e1 : ((-1 : C) ^ s₀) ^ l = (-1) ^ s₀ := by
      rw [← pow_mul, mul_comm, pow_mul, hodd.neg_one_pow]
    rw [e1, pow_add, pow_one, mul_comm l (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u), pow_mul, inv_pow,
      pow_succ (-1 : C)]
    field_simp
  have hsum : ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ c,
      be c n b * MvPowerSeries.coeff α (if n = 1 ∧ c ∈ Gs s₀ then P c else 0) =
      ∑ c ∈ Gs s₀, be c 1 b * MvPowerSeries.coeff α (P c) := by
    by_cases hα : α = 0
    · subst hα
      have : ∀ c, MvPowerSeries.coeff (0 : Fin M →₀ ℕ) (P c) = 0 := by
        intro c
        simp [hP, hl.ne_zero]
      simp only [this, mul_zero, Finset.sum_const_zero]
      simp
    · rw [Finset.sum_eq_single 1]
      · simp only [true_and]
        rw [← Finset.sum_subset (Finset.subset_univ (Gs s₀))]
        · exact Finset.sum_congr rfl fun c hc => by rw [if_pos hc]
        · intro c _ hc
          simp [hc]
      · intro n _ hn
        simp [hn]
      · intro h
        exfalso
        apply h
        have : Finsupp.degree α ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
        rw [Finset.mem_range]; omega
  rw [map_sub, hζ, hmain, ← hsum, ← neg_sub', v.map_neg, ← Finset.sum_sub_distrib]
  apply v.map_le_sum
  intro n _
  rw [← Finset.sum_sub_distrib]
  apply v.map_le_sum
  intro c _
  rw [← mul_sub, ← map_sub]
  exact hterm n c

end GlobalTheory
