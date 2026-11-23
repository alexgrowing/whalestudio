import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PsWeightCalculus
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightedOrderGePrimePowOfSumPurePowersAdd

open ReciprocityTheory.PGsh MvPowerSeries

namespace GlobalTheory.ChainCoord

section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

theorem ord_mono {g : MvPowerSeries (Fin M) C} {w w' : ℝ} (h : OrdGe v ρ g w) (hw : w' ≤ w) :
    OrdGe v ρ g w' := fun α =>
  le_trans (WithTop.coe_le_coe.2 (by linarith)) (h α)

theorem ord_zero (w : ℝ) : OrdGe v ρ (0 : MvPowerSeries (Fin M) C) w := fun α => by
  simp

theorem ord_add {g g' : MvPowerSeries (Fin M) C} {w : ℝ} (h : OrdGe v ρ g w)
    (h' : OrdGe v ρ g' w) : OrdGe v ρ (g + g') w := fun α => by
  rw [map_add]
  exact le_trans (le_min (h α) (h' α)) (v.map_add _ _)

theorem ord_neg {g : MvPowerSeries (Fin M) C} {w : ℝ} (h : OrdGe v ρ g w) :
    OrdGe v ρ (-g) w := fun α => by
  rw [map_neg, v.map_neg]
  exact h α

theorem ord_sum {ι : Type*} (s : Finset ι) {g : ι → MvPowerSeries (Fin M) C} {w : ℝ}
    (h : ∀ i ∈ s, OrdGe v ρ (g i) w) : OrdGe v ρ (∑ i ∈ s, g i) w :=
  Finset.sum_induction g (fun x => OrdGe v ρ x w) (fun _ _ => ord_add) (ord_zero w) h

theorem ord_C_mul {g : MvPowerSeries (Fin M) C} {w a : ℝ} {x : C} (hx : (a : WithTop ℝ) ≤ v x)
    (h : OrdGe v ρ g w) : OrdGe v ρ (MvPowerSeries.C (R := C) x * g) (a + w) := fun α => by
  rw [coeff_C_mul, v.map_mul, add_sub_assoc, WithTop.coe_add]
  exact add_le_add hx (h α)

theorem ord_pow {g : MvPowerSeries (Fin M) C} {w : ℝ} (h : OrdGe v ρ g w) (N : ℕ) :
    OrdGe v ρ (g ^ N) (N * w) := fun α => by
  have e : ∀ β : Fin M →₀ ℕ, β.sum (fun j e => ρ j * (e : ℝ)) = ∑ m, ρ m * β m := fun β =>
    Finsupp.sum_fintype _ _ (by simp)
  have := (GlobalTheory.psWeight_calculus C v (Fin M) ρ g g w w (fun β => by rw [e]; exact h β)).2 N α
  rwa [e] at this

theorem ord_pure {r w : ℝ} {N : ℕ} {a : Fin M → C}
    (h : ∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) :
    OrdGe v (fun _ => r) (∑ j, MvPowerSeries.C (R := C) (a j) *
      (X j : MvPowerSeries (Fin M) C) ^ N) w := by
  refine ord_sum _ fun j _ α => ?_
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hα
  · subst hα
    rw [mul_one, Finset.sum_eq_single j (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (by simp)]
    simpa using h j
  · simp

theorem coeff_pow_congr {f g : MvPowerSeries (Fin M) C} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {D m : ℕ} (hm : 2 ≤ m)
    (h : ∀ β : Fin M →₀ ℕ, Finsupp.degree β < D → coeff β f = coeff β g)
    (α : Fin M →₀ ℕ) (hα : Finsupp.degree α = D) : coeff α (f ^ m) = coeff α (g ^ m) := by
  rw [← sub_eq_zero, ← map_sub, ← (Commute.all f g).mul_geom_sum₂ m]
  apply coeff_of_lt_order
  have h1 : (D : ℕ∞) ≤ (f - g).order := nat_le_order fun β hβ => by
    rw [map_sub, h β hβ, sub_self]
  have h2 : ((1 : ℕ) : ℕ∞) ≤ (∑ i ∈ Finset.range m, f ^ i * g ^ (m - 1 - i)).order :=
    nat_le_order fun β hβ => by
      have : β = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]; omega
      subst this
      rw [coeff_zero_eq_constantCoeff_apply, map_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [map_mul, map_pow, map_pow, hf, hg, ← pow_add, zero_pow]
      have := Finset.mem_range.1 hi
      omega
  refine lt_of_lt_of_le ?_ (le_trans (add_le_add h1 h2) le_order_mul)
  rw [hα]
  exact_mod_cast Nat.lt_succ_self D

theorem coeff_pow_eq_zero {f : MvPowerSeries (Fin M) C} (hf : constantCoeff f = 0) {m : ℕ}
    (α : Fin M →₀ ℕ) (hα : Finsupp.degree α < m) : coeff α (f ^ m) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero m hf)
  exact_mod_cast hα

theorem coeff_lgSum {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0) (e : Fin d)
    (α : Fin M →₀ ℕ) (N : ℕ) (hN : Finsupp.degree α < N) :
    coeff α (lgSum l al t e) =
      ∑ n ∈ Finset.range N, ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := by
  change ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, al a n e * coeff α (t a ^ (l ^ n)) = _
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun n _ hn => ?_
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [coeff_pow_eq_zero (ht a), mul_zero]
  have h1 : n < l ^ n := Nat.lt_pow_self hl
  simp only [Finset.mem_range] at hn
  omega

theorem v_inv_pow {x : C} (hx : v x = 1) (E : ℕ) :
    ((-(E : ℝ) : ℝ) : WithTop ℝ) ≤ v ((x ^ E)⁻¹) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at hx
    exact WithTop.top_ne_one hx
  have h1 : v ((x ^ E)⁻¹) + v (x ^ E) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ (pow_ne_zero _ hx0), v.map_one]
  have h2 : v (x ^ E) = ((E : ℝ) : WithTop ℝ) := by
    rw [v.map_pow, hx, ← WithTop.coe_one, ← WithTop.coe_nsmul]; simp
  rw [h2] at h1
  cases hv : v ((x ^ E)⁻¹) with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h1
    exact WithTop.coe_le_coe.2 (by linarith)

theorem ord_of_step {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (h0 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (t μ z : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0)
    (hμ : ∀ c, constantCoeff (μ c) = 0) (hz : ∀ e, lgSum l al t e = z e) (w : ℝ)
    (step : ∀ t' : Fin d → MvPowerSeries (Fin M) C, (∀ c, OrdGe v ρ (t' c - μ c) w) →
      ∀ N e, OrdGe v ρ (z e - (∑ n ∈ Finset.range (N + 2), ∑ c,
        MvPowerSeries.C (R := C) (al c (n + 1) e) * t' c ^ (l ^ (n + 1))) - μ e) w) :
    ∀ c, OrdGe v ρ (t c - μ c) w := by
  classical
  have key : ∀ D : ℕ, ∀ α : Fin M →₀ ℕ, Finsupp.degree α = D → ∀ c,
      (((w - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α (t c - μ c)) := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro α hα e
      let ν : Fin d → MvPowerSeries (Fin M) C := fun c β =>
        if Finsupp.degree β < D then coeff β (t c - μ c) else 0
      have hν : ∀ c β, coeff β (ν c) =
          if Finsupp.degree β < D then coeff β (t c - μ c) else 0 := fun _ _ => rfl
      have h1 : ∀ c, OrdGe v ρ (μ c + ν c - μ c) w := fun c β => by
        rw [add_sub_cancel_left, hν]
        split_ifs with hβ
        · exact ih _ hβ β rfl c
        · simp
      have h2 := step (fun c => μ c + ν c) h1 D e α
      have h3 : ∀ c, constantCoeff (μ c + ν c) = 0 := fun c => by
        rw [map_add, hμ, zero_add, ← coeff_zero_eq_constantCoeff_apply, hν]
        split_ifs
        · rw [coeff_zero_eq_constantCoeff_apply, map_sub, ht, hμ, sub_self]
        · rfl
      have h4 : ∀ c n, coeff α ((μ c + ν c) ^ (l ^ (n + 1))) = coeff α (t c ^ (l ^ (n + 1))) :=
        fun c n => by
          refine coeff_pow_congr (h3 c) (ht c) ?_ (fun β hβ => ?_) α hα
          · exact le_trans hl (Nat.le_self_pow (by omega) l)
          · rw [map_add, hν, if_pos hβ, map_sub]; ring
      have h5 := coeff_lgSum hl al t ht e α (D + 2 + 1) (by omega)
      rw [hz, Finset.sum_range_succ'] at h5
      simp only [h0, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h5
      convert h2 using 2
      simp only [map_sub, map_sum, coeff_C_mul, h4, h5]
      ring
  exact fun c α => key _ α rfl c

end

theorem geom_real {l : ℕ} (hl : 3 ≤ l) (s : ℕ) :
    ((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) =
      (((l : ℝ) ^ 2) ^ s - 1) * (1 / ((l : ℝ) ^ 2 - 1)) := by
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  push_cast
  rw [← geom_sum_mul]
  field_simp

theorem high_real {l : ℕ} (hl : 3 ≤ l) (k : ℕ) :
    1 + 1 / ((l : ℝ) ^ 2 - 1) ≤
      (1 - ((k + 3 : ℕ) : ℝ)) + ((l ^ (k + 3) : ℕ) : ℝ) * (1 / ((l : ℝ) ^ 2 - 1)) := by
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have h : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have h1 : k + 3 ≤ l ^ (k + 1) := by
    have : k < l ^ k := Nat.lt_pow_self (by omega)
    rw [pow_succ]; nlinarith
  have h2 : ((k : ℝ) + 3) ≤ (l : ℝ) ^ (k + 1) := by exact_mod_cast h1
  have h4 : ((k : ℝ) + 3) ≤ ((l : ℝ) ^ (k + 3) - 1) * (1 / ((l : ℝ) ^ 2 - 1)) := by
    rw [mul_one_div, le_div_iff₀ h, show (l : ℝ) ^ (k + 3) = (l : ℝ) ^ (k + 1) * l ^ 2 by ring]
    have : (0 : ℝ) ≤ k := by positivity
    nlinarith
  push_cast
  linarith

section
variable {C : Type} [Field C]

noncomputable def kap (C : Type) [Field C] (l s : ℕ) : C :=
  (-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹

theorem v_kap {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hv : v (l : C) = 1) (s : ℕ) :
    ((-((∑ u ∈ Finset.range s, (l ^ 2) ^ u : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v (kap C l s) := by
  have : v ((-1 : C) ^ s) = 0 := by rw [v.map_pow, v.map_neg, v.map_one, smul_zero]
  rw [kap, v.map_mul, this, zero_add]
  exact v_inv_pow hv _

theorem kap_succ {l : ℕ} (ho : Odd l) (s : ℕ) :
    kap C l (s + 1) = -((l : C)⁻¹ * kap C l s ^ (l ^ 2)) := by
  have h1 : ((-1 : C) ^ s) ^ (l ^ 2) = (-1) ^ s := by
    rw [← pow_mul, mul_comm, pow_mul, (ho.pow (n := 2)).neg_one_pow]
  have h2 : ∑ u ∈ Finset.range (s + 1), (l ^ 2) ^ u =
      (∑ u ∈ Finset.range s, (l ^ 2) ^ u) * l ^ 2 + 1 := by
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp [pow_succ (l ^ 2)]
  rw [kap, kap, mul_pow, h1, h2, inv_pow, ← pow_mul, pow_succ (l : C), mul_inv]
  ring

noncomputable def pure {d M : ℕ} (l : ℕ) (π : ℕ → Fin d → Fin M → C) (s : ℕ) (c : Fin d) :
    MvPowerSeries (Fin M) C :=
  ∑ j, MvPowerSeries.C (R := C) (kap C l s * π s c j) *
    (X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)

theorem ord_pure_level {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : 3 ≤ l)
    (hv : v (l : C) = 1) {d M : ℕ} {π : ℕ → Fin d → Fin M → C} {s : ℕ} {c : Fin d} {a σ : ℝ}
    (h : ∀ j, (a : WithTop ℝ) ≤ v (π s c j)) (j : Fin M) :
    ((a + 1 / ((l : ℝ) ^ 2 - 1) + ((l : ℝ) ^ 2) ^ s * σ -
      (1 / ((l : ℝ) ^ 2 - 1) + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
        v (kap C l s * π s c j) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add (v_kap hv s) (h j))
  rw [← WithTop.coe_add, geom_real hl]
  refine WithTop.coe_le_coe.2 (le_of_eq ?_)
  push_cast
  ring

end

theorem chain :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) →
    (∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c - ∑ j, MvPowerSeries.C (R := C) ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)) (1 + 1 / ((l : ℝ) ^ 2 - 1))) ∧
    ∀ c, (∀ s ≤ s₀, c ∉ Gs s) → OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c) (1 + 1 / ((l : ℝ) ^ 2 - 1))) := by
  intro C _ _ v l hp hv hl d M s₀ good Gs al π t hgood huniq h0 hall hg hout hπ0 hπ0' hπ ht hz
  classical
  have h3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hq : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hl0 : (l : C) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 / ((l : ℝ) ^ 2 - 1) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hρq : (l : ℝ) ^ 2 * ρ = 1 + ρ := by rw [hρ]; field_simp; ring
  have hσq : ((l : ℝ) ^ 2) ^ (s₀ + 1) * σ = 3 * l / 8 := by rw [hσ]; field_simp; ring
  have hv1 : ((1 : ℝ) : WithTop ℝ) ≤ v (l : C) := by rw [hv]; simp

  have hint : ∀ s c j, ((0 : ℝ) : WithTop ℝ) ≤ v (π s c j) := by
    intro s
    induction s with
    | zero => exact hπ0
    | succ s ih =>
      intro e j
      rw [hπ]
      refine v.map_le_sum fun c hc => ?_
      rw [v.map_mul, v.map_mul, v.map_pow]
      have h1 := ((hg c (hgood s c hc)).2 2 e (by norm_num))
      refine le_trans ?_ (add_le_add (add_le_add hv1 h1) (nsmul_nonneg (ih c j) _))
      rw [← WithTop.coe_add]
      norm_num
  have hint1 : ∀ s < s₀, ∀ e, e ∉ Gs (s + 1) → ∀ j,
      ((1 : ℝ) : WithTop ℝ) ≤ v (π (s + 1) e j) := by
    intro s hs e he j
    rw [hπ]
    refine v.map_le_sum fun c hc => ?_
    rw [v.map_mul, v.map_mul, v.map_pow]
    refine le_trans ?_ (add_le_add (add_le_add hv1 (hout s hs c hc e he))
      (nsmul_nonneg (hint s c j) _))
    simp
  have hlev : ∀ (s : ℕ) (c : Fin d) (a : ℝ), (∀ j, (a : WithTop ℝ) ≤ v (π s c j)) → ∀ j,
      ((a + ρ + ((l : ℝ) ^ 2) ^ s * σ - (ρ + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
        v (kap C l s * π s c j) := fun s c a h j => by
    rw [hρ]; exact ord_pure_level hl hv h j
  have hP : ∀ (s : ℕ) (c : Fin d) (a : ℝ), (∀ j, (a : WithTop ℝ) ≤ v (π s c j)) →
      OrdGe v (fun _ => ρ + σ) (pure l π s c) (a + ρ + ((l : ℝ) ^ 2) ^ s * σ) :=
    fun s c a h => ord_pure (hlev s c a h)
  let μ : Fin d → MvPowerSeries (Fin M) C := fun c =>
    ∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then pure l π s c else 0
  have hsel : ∀ (f : ℕ → MvPowerSeries (Fin M) C) s, s ≤ s₀ → ∀ c ∈ Gs s,
      (∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then f s else 0) = f s := by
    intro f s hs c hc
    rw [Finset.sum_eq_single s, if_pos hc]
    · intro b hb hbs
      rw [if_neg]
      intro h
      exact hbs (huniq b s c (by simpa [Nat.lt_succ_iff] using hb) hs h hc)
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hsel0 : ∀ (f : ℕ → MvPowerSeries (Fin M) C) c, (∀ s ≤ s₀, c ∉ Gs s) →
      (∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then f s else 0) = 0 := fun f c hc =>
    Finset.sum_eq_zero fun s hs => if_neg (hc s (by simpa [Nat.lt_succ_iff] using hs))
  have main : ∀ c, OrdGe v (fun _ => ρ + σ) (t c - μ c) (1 + ρ) := by
    refine ord_of_step (by omega) al h0 t μ _ ht (fun c => ?_) hz _ ?_
    · simp only [μ, map_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      split_ifs
      · simp only [pure, map_sum, map_mul, map_pow, constantCoeff_X]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [zero_pow (by positivity), mul_zero]
      · simp
    intro t' ht' N e
    let F : ℕ → Fin d → MvPowerSeries (Fin M) C := fun s c =>
      MvPowerSeries.C (R := C) (al c 2 e) *
        ∑ j, MvPowerSeries.C (R := C) ((kap C l s * π s c j) ^ (l ^ 2)) *
          (X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s * l ^ 2)
    let G : Fin d → MvPowerSeries (Fin M) C := fun c =>
      ∑ s ∈ Finset.range (s₀ + 1), if c ∈ Gs s then F s c else 0
    have hF : ∀ s, ∑ c ∈ Gs s, F s c = - pure l π (s + 1) e := by
      intro s
      simp only [F, pure, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_succ, ← neg_mul, ← map_neg, hπ, kap_succ (hp.odd_of_ne_two (by omega)),
        Finset.mul_sum, ← Finset.sum_neg_distrib, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_assoc, ← map_mul]
      congr 2
      rw [mul_pow]
      field_simp
    have hG : ∑ c, G c = - ∑ s ∈ Finset.range (s₀ + 1), pure l π (s + 1) e := by
      simp only [G]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← hF, Finset.sum_ite_mem, Finset.univ_inter]
    have hz0 : (∑ j, MvPowerSeries.C (R := C) (π 0 e j) * (X j : MvPowerSeries (Fin M) C)) =
        pure l π 0 e := by
      simp [pure, kap]
    have hA : OrdGe v (fun _ => ρ + σ)
        (∑ s ∈ Finset.range (s₀ + 1), (pure l π s e - if e ∈ Gs s then pure l π s e else 0))
        (1 + ρ) := by
      refine ord_sum _ fun s hs => ?_
      split_ifs with he
      · rw [sub_self]; exact ord_zero _
      · rw [sub_zero]
        cases s with
        | zero =>
          have : pure l π 0 e = 0 := by simp [pure, hπ0' e he]
          rw [this]; exact ord_zero _
        | succ s =>
          refine ord_mono (hP _ _ 1 (hint1 s (by simpa using hs) e he)) ?_
          have : 0 ≤ ((l : ℝ) ^ 2) ^ (s + 1) * σ := by positivity
          linarith
    have hB : OrdGe v (fun _ => ρ + σ) (pure l π (s₀ + 1) e) (1 + ρ) :=
      ord_mono (hP _ _ 0 (hint _ e)) (by rw [hσq]; linarith)
    have hT : ∀ n c, OrdGe v (fun _ => ρ + σ)
        (MvPowerSeries.C (R := C) (al c (n + 1) e) * t' c ^ (l ^ (n + 1)) -
          if n = 1 then G c else 0) (1 + ρ) := by
      intro n c
      by_cases hc : ∃ s ≤ s₀, c ∈ Gs s
      · obtain ⟨s, hs, hc⟩ := hc
        have hν := ht' c
        have hμ : μ c = pure l π s c := hsel (fun s => pure l π s c) s hs c hc
        rw [hμ] at hν
        obtain ⟨hg1, hg2⟩ := hg c (hgood s c hc)
        have hqs : 0 ≤ ((l : ℝ) ^ 2) ^ s * σ := by positivity
        match n with
        | 0 => simp [hg1, ord_zero]
        | 1 =>
          have hGc : G c = F s c := hsel (fun s => F s c) s hs c hc
          have h1 := GlobalTheory.WeightFrobenius.main C v l hp hv M ((l ^ 2) ^ s) 2 (ρ + σ) ρ (1 + ρ)
            (fun j => kap C l s * π s c j) (t' c - pure l π s c) (by linarith)
            (fun j => le_trans (WithTop.coe_le_coe.2 (by linarith)) (hlev s c 0 (hint s c) j)) hν
          have h2 := ord_C_mul (hg2 2 e (by norm_num)) h1
          rw [if_pos rfl, hGc]
          refine ord_mono (w := _) (by
            convert h2 using 1
            simp only [F, pure, add_sub_cancel, mul_sub]) ?_
          rw [mul_add, hρq]
          rcases min_cases (1 + (1 + ρ)) ((l : ℝ) ^ 2 * 1 + (1 + ρ)) with h | h <;>
            rw [h.1] <;> push_cast <;> nlinarith
        | k + 2 =>
          rw [if_neg (by omega), sub_zero]
          have h1 : OrdGe v (fun _ => ρ + σ) (t' c) ρ := by
            have := ord_add (ord_mono hν (by linarith : ρ ≤ 1 + ρ))
              (ord_mono (hP s c 0 (hint s c)) (by linarith : ρ ≤ _))
            rwa [sub_add_cancel] at this
          refine ord_mono (ord_C_mul (hg2 _ e (by omega)) (ord_pow h1 _)) ?_
          rw [hρ]
          exact high_real hl k
      · push_neg at hc
        have hν := ht' c
        have hμ : μ c = 0 := hsel0 (fun s => pure l π s c) c hc
        have hGc : G c = 0 := hsel0 (fun s => F s c) c hc
        rw [hμ, sub_zero] at hν
        rw [hGc, ite_self, sub_zero]
        refine ord_mono (ord_C_mul (hall c _ e) (ord_pow hν _)) ?_
        have h1 : n + 1 < l ^ (n + 1) := Nat.lt_pow_self (by omega)
        have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ ((l ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        have h4 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        nlinarith
    have hS := ord_sum (Finset.range (N + 2)) fun n _ => ord_sum Finset.univ fun c _ => hT n c
    have hfin := ord_add (ord_add hA hB) (ord_neg hS)
    convert hfin using 1
    have hi : ∑ n ∈ Finset.range (N + 2), ∑ c, (if n = 1 then G c else 0) = ∑ c, G c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq', if_pos (by simp)]
    have hs : ∑ s ∈ Finset.range (s₀ + 1), pure l π (s + 1) e + pure l π 0 e =
        ∑ s ∈ Finset.range (s₀ + 1), pure l π s e + pure l π (s₀ + 1) e := by
      rw [← Finset.sum_range_succ' (fun s => pure l π s e), Finset.sum_range_succ]
    simp only [Finset.sum_sub_distrib, hi, hG, hz0]
    linear_combination hs
  rw [← hρ, ← hσ]
  refine ⟨fun s hs c hc => ?_, fun c hc => ?_⟩
  · have := main c
    rwa [show μ c = pure l π s c from hsel (fun s => pure l π s c) s hs c hc] at this
  · have := main c
    rwa [show μ c = 0 from hsel0 (fun s => pure l π s c) c hc, sub_zero] at this

end GlobalTheory.ChainCoord
