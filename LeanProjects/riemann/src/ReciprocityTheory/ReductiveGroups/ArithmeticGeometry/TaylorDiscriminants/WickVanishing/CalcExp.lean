import Mathlib

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

section Two

variable (k : Type) [CommRing k] [Algebra ℚ k]

theorem fin_two_finsupp_eq_iff (e : Fin 2 →₀ ℕ) (m l : ℕ) :
    e = Finsupp.single 0 m + Finsupp.single 1 l ↔ e 0 = m ∧ e 1 = l := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

theorem coeff_X_add_X_pow (e : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff e (((X 0 : MvPowerSeries (Fin 2) k) + X 1) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : k) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      MvPowerSeries.coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (n - m) *
        (n.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = n - m then (n.choose m : k) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial]
    by_cases h : e 0 = m ∧ e 1 = n - m
    · rw [if_pos h, if_pos ((fin_two_finsupp_eq_iff e m (n - m)).2 h)]; simp
    · rw [if_neg h, if_neg (fun h' => h ((fin_two_finsupp_eq_iff e m (n - m)).1 h'))]; simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hn
  · rw [Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg (fun h => hm h.1.symm)]
    · intro h
      exfalso; exact h (Finset.mem_range.mpr (by omega))
  · apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg (fun h => hn (by omega))]

theorem exp_two :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (PowerSeries.exp k) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  have hX : ∀ i : Fin 2, ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
        if d = Finsupp.single i (d i) then algebraMap ℚ k (1 / (d i).factorial) else 0 := by
    intro i d
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i), finsum_eq_single _ (d i)]
    · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, PowerSeries.coeff_exp]
      split_ifs <;> simp
    · intro m hm
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
      intro h; apply hm; rw [h]; simp
  ext e
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [hX, hX, if_pos (by simp), if_pos (by simp)]
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_X_add_X_pow, if_pos rfl, PowerSeries.coeff_exp]
      simp only [Finsupp.single_eq_same, smul_eq_mul]
      rw [← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
      congr 1
      have hf0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
      rw [Nat.add_sub_cancel_left] at hf0
      have hf : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * (e 0).factorial * (e 1).factorial =
          (e 0 + e 1).factorial := by exact_mod_cast hf0
      have ha : ((e 0).factorial : ℚ) ≠ 0 := by positivity
      have hb : ((e 1).factorial : ℚ) ≠ 0 := by positivity
      have hc : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      rw [← hf]
      field_simp
    · intro m hm
      rw [coeff_X_add_X_pow, if_neg (Ne.symm hm), smul_zero]
  · rintro ⟨p, q⟩ hpq' hne
    have hpq : p + q = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq'
    dsimp only
    rw [hX, hX]
    by_cases hp : p = Finsupp.single 0 (p 0)
    · by_cases hq : q = Finsupp.single 1 (q 1)
      · exfalso; apply hne
        have h0 : p 0 = e 0 := by rw [← hpq, hp, hq]; simp
        have h1 : q 1 = e 1 := by rw [← hpq, hp, hq]; simp
        rw [hp, hq, h0, h1]
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  · intro h; exfalso; apply h
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_finsupp_eq_iff e (e 0) (e 1)).2 ⟨rfl, rfl⟩).symm

end Two

section General

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem hasSubst_two {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ k) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [ha, hb])

theorem subst_two_psubst {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (Y : MvPowerSeries (Fin 2) k) (hY : constantCoeff Y = 0) (f : PowerSeries k) :
    MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) (PowerSeries.subst Y f) =
      PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ k) Y) f := by
  have hY' := (PowerSeries.HasSubst.of_constantCoeff_zero hY).const
  exact MvPowerSeries.subst_comp_subst_apply hY' (hasSubst_two ha hb) f

theorem exp_add {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (a + b) (PowerSeries.exp k) =
      PowerSeries.subst a (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) := by
  have hab := hasSubst_two ha hb
  have h0 : constantCoeff ((X 0 : MvPowerSeries (Fin 2) k) + X 1) = 0 := by simp
  have e1 := subst_two_psubst ha hb _ h0 (PowerSeries.exp k)
  rw [exp_two k, MvPowerSeries.subst_mul hab, subst_two_psubst ha hb _ (by simp),
    subst_two_psubst ha hb _ (by simp), MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab,
    MvPowerSeries.subst_X hab] at e1
  simpa using e1.symm

theorem constantCoeff_psubst {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) (f : PowerSeries k) :
    constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : f = PowerSeries.C (PowerSeries.constantCoeff f) +
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add,
    PowerSeries.constantCoeff_subst_eq_zero ha _ (by simp), add_zero]
  simp

theorem constantCoeff_exp {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    constantCoeff (PowerSeries.subst a (PowerSeries.exp k)) = 1 := by
  rw [constantCoeff_psubst ha, PowerSeries.constantCoeff_exp]

private theorem powerSeries_subst_zero_eq_C_constantCoeff (f : PowerSeries k) :
    PowerSeries.subst (0 : MvPowerSeries σ k) f = MvPowerSeries.C (PowerSeries.constantCoeff f) := by
  classical
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  by_cases he : e = 0
  · subst he; simp
  · simp only [smul_eq_mul, pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [MvPowerSeries.coeff_one, if_neg he, mul_zero, MvPowerSeries.coeff_C, if_neg he]

private theorem powerSeries_subst_one (a : MvPowerSeries σ k) :
    PowerSeries.subst a (1 : PowerSeries k) = 1 := by
  rw [show (1 : PowerSeries k) = PowerSeries.C (1 : k) from (map_one _).symm, PowerSeries.subst_C,
    map_one]

theorem exp_zero : PowerSeries.subst (0 : MvPowerSeries σ k) (PowerSeries.exp k) = 1 := by
  rw [powerSeries_subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]

end General

section Inj

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem natCast_mul_eq_zero {x : k} {n : ℕ} (hn : n ≠ 0) (h : (n : k) * x = 0) : x = 0 := by
  have hu : IsUnit (n : k) := by
    rw [← map_natCast (algebraMap ℚ k)]
    exact (IsUnit.mk0 _ (by exact_mod_cast hn)).map _
  exact hu.mul_right_eq_zero.mp h

private theorem one_add_X_mul_derivative_log_eq_one :
    (1 + PowerSeries.X) * PowerSeries.derivative k (PowerSeries.log k) = 1 := by
  have hD : ∀ n : ℕ,
      PowerSeries.coeff n (PowerSeries.derivative k (PowerSeries.log k)) = (-1 : k) ^ n := by
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero n)]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    rw [show ((n : k) + 1) = algebraMap ℚ k ((n : ℚ) + 1) by simp, ← map_mul]
    rw [show ((-1 : ℚ) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℚ)) * ((n : ℚ) + 1) = (-1) ^ n by
      push_cast; rw [div_mul_cancel₀ _ hn]; ring]
    simp
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [hD, PowerSeries.coeff_one]
  · rw [PowerSeries.coeff_succ_X_mul, hD, hD, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
    ring

private theorem constantCoeff_log_eq_zero_wick_vanishing : PowerSeries.constantCoeff (PowerSeries.log k) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_log]
  simp

private theorem isAddTorsionFree_coeff_ring : IsAddTorsionFree k := by
  first
  | infer_instance
  | exact ⟨fun n hn a b hab => by
      have h2 : (n : k) * (a - b) = 0 := by
        simp only [nsmul_eq_mul] at hab; rw [mul_sub, hab, sub_self]
      exact sub_eq_zero.mp (natCast_mul_eq_zero hn h2)⟩

private theorem subst_exp_sub_one_log_eq_X :
    PowerSeries.subst (PowerSeries.exp k - 1) (PowerSeries.log k) = PowerSeries.X := by
  haveI := isAddTorsionFree_coeff_ring (k := k)
  have hs : PowerSeries.HasSubst (PowerSeries.exp k - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst hs, PowerSeries.derivative_X, map_sub,
      PowerSeries.derivative_exp, Derivation.map_one_eq_zero, sub_zero]
    have h1 := congrArg (PowerSeries.subst (PowerSeries.exp k - 1)) (one_add_X_mul_derivative_log_eq_one (k := k))
    rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs, powerSeries_subst_one, PowerSeries.subst_X hs] at h1
    linear_combination h1
  · rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_sub, map_one]; exact sub_eq_zero.mpr PowerSeries.constantCoeff_exp) _ constantCoeff_log_eq_zero_wick_vanishing

private theorem subst_log_subst_exp_sub_one_eq_self {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a := by
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.subst a (PowerSeries.exp k) - 1 =
      PowerSeries.subst a (PowerSeries.exp k - 1) := by
    have h2 := PowerSeries.subst_add ha' (PowerSeries.exp k - 1) 1
    rw [sub_add_cancel, powerSeries_subst_one] at h2
    rw [h2]; ring
  have hs : PowerSeries.HasSubst (PowerSeries.exp k - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [h1, ← PowerSeries.subst_comp_subst_apply hs ha', subst_exp_sub_one_log_eq_X, PowerSeries.subst_X ha']

theorem eq_zero_of_exp_eq_one {c : MvPowerSeries σ k} (hc : constantCoeff c = 0)
    (h : PowerSeries.subst c (PowerSeries.exp k) = 1) : c = 0 := by
  have h1 := subst_log_subst_exp_sub_one_eq_self hc
  rw [h, sub_self, powerSeries_subst_zero_eq_C_constantCoeff, constantCoeff_log_eq_zero_wick_vanishing, map_zero] at h1
  exact h1.symm

theorem exp_inj {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (h : PowerSeries.subst a (PowerSeries.exp k) = PowerSeries.subst b (PowerSeries.exp k)) : a = b := by
  have hab : constantCoeff (a - b) = 0 := by simp [ha, hb]
  have h1 := exp_add hab hb
  rw [sub_add_cancel, h] at h1
  have hu : IsUnit (PowerSeries.subst b (PowerSeries.exp k)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_exp hb]; exact isUnit_one)
  have h3 : 1 * PowerSeries.subst b (PowerSeries.exp k) =
      PowerSeries.subst (a - b) (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k) :=
    (one_mul _).trans h1
  exact sub_eq_zero.mp (eq_zero_of_exp_eq_one hab (hu.mul_right_cancel h3).symm)

end Inj

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

private theorem eq_zero_of_one_add_X_mul_derivative_eq_self' (H : PowerSeries k) (h0 : PowerSeries.constantCoeff H = 0)
    (h : (1 + PowerSeries.X) * PowerSeries.derivative k H = H) : H = 0 := by
  have hc : ∀ n, PowerSeries.coeff n H = 0 := by
    intro n
    induction n with
    | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h0
    | succ n ih =>
      have h1 := congrArg (PowerSeries.coeff n) h
      have hX : PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative k H) = 0 := by
        rcases n with _ | m
        · simp
        · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, ih, zero_mul]
      rw [add_mul, one_mul, map_add, hX, add_zero, PowerSeries.coeff_derivative, ih] at h1
      have h2 : ((n + 1 : ℕ) : k) * PowerSeries.coeff (n + 1) H = 0 := by
        rw [mul_comm]; push_cast; exact h1
      exact natCast_mul_eq_zero (Nat.succ_ne_zero n) h2
  ext n
  simp [hc n]

theorem exp_log_one_add : PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) = 1 + PowerSeries.X := by
  have hL : PowerSeries.HasSubst (PowerSeries.log k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_log_eq_zero_wick_vanishing
  have hD : PowerSeries.derivative k (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) =
      PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) *
        PowerSeries.derivative k (PowerSeries.log k) := by
    rw [PowerSeries.derivative_subst hL, PowerSeries.derivative_exp]
  have hE0 : PowerSeries.constantCoeff
      (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) = 1 := by
    have h1 := constantCoeff_psubst (σ := Unit) (a := PowerSeries.log k) constantCoeff_log_eq_zero_wick_vanishing (PowerSeries.exp k)
    rw [PowerSeries.constantCoeff_exp] at h1
    exact h1
  have hH := eq_zero_of_one_add_X_mul_derivative_eq_self' (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) -
    (1 + PowerSeries.X)) (by simp [hE0]) (by
      rw [map_sub, map_add, hD, PowerSeries.derivative_X, Derivation.map_one_eq_zero, zero_add]
      linear_combination (PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k)) * one_add_X_mul_derivative_log_eq_one (k := k))
  exact sub_eq_zero.mp hH

theorem constantCoeff_logS {f : MvPowerSeries σ k} (hf : constantCoeff f = 1) :
    constantCoeff (PowerSeries.subst (f - 1) (PowerSeries.log k)) = 0 := PowerSeries.constantCoeff_subst_eq_zero (by simp [hf]) _ constantCoeff_log_eq_zero_wick_vanishing

theorem exp_log {f : MvPowerSeries σ k} (hf : constantCoeff f = 1) :
    PowerSeries.subst (PowerSeries.subst (f - 1) (PowerSeries.log k)) (PowerSeries.exp k) = f := by
  have hb : PowerSeries.HasSubst (f - 1) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hf])
  have ha : PowerSeries.HasSubst (PowerSeries.log k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_log_eq_zero_wick_vanishing
  rw [← PowerSeries.subst_comp_subst_apply ha hb, exp_log_one_add, PowerSeries.subst_add hb,
    PowerSeries.subst_X hb, powerSeries_subst_one]
  ring

theorem log_exp {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a := subst_log_subst_exp_sub_one_eq_self ha

end Log

section Props

theorem subst_exp {k : Type} [CommRing k] [Algebra ℚ k] {σ τ : Type} [Finite σ] (φ : σ → MvPowerSeries τ k)
    (hφ : ∀ s, constantCoeff (φ s) = 0) {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k) := by
  have ha' := (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  exact MvPowerSeries.subst_comp_subst_apply ha' (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ) _

def ExpAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a b : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff b = 0 → PowerSeries.subst (a + b) (PowerSeries.exp k) =
      PowerSeries.subst a (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k)

def ExpConstSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff (PowerSeries.subst a (PowerSeries.exp k)) = 1

def ExpInjSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a b : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff b = 0 → PowerSeries.subst a (PowerSeries.exp k) = PowerSeries.subst b (PowerSeries.exp k) → a = b

def ExpLogSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (f : MvPowerSeries σ k), constantCoeff f = 1 →
    constantCoeff (PowerSeries.subst (f - 1) (PowerSeries.log k)) = 0 ∧
      PowerSeries.subst (PowerSeries.subst (f - 1) (PowerSeries.log k)) (PowerSeries.exp k) = f

def LogExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a : MvPowerSeries σ k), constantCoeff a = 0 →
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a

def SubstExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ τ : Type) [Finite σ] (φ : σ → MvPowerSeries τ k)
    (a : MvPowerSeries σ k), (∀ s, constantCoeff (φ s) = 0) → constantCoeff a = 0 →
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k)

end Props

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
