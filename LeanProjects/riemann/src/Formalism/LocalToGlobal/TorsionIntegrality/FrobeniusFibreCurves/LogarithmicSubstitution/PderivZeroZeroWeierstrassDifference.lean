import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1)

namespace Add0

section

variable {K : Type} [Field K] [CharZero K]

local notation "A2" => MvPowerSeries (Fin 2) K

theorem triple_lintegral_eq (x : Fin 2) (f : PowerSeries K) :
    (at1 x f : A2) = PowerSeries.substAlgHom (PowerSeries.HasSubst.X x) f := by
  rw [PowerSeries.coe_substAlgHom]
  rfl

private theorem coeff_at1_fin_two_eq_ite (x : Fin 2) (f : PowerSeries K) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (at1 x f : A2) = if d = Finsupp.single x (d x) then PowerSeries.coeff (d x) f else 0 := by
  classical
  unfold at1
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X x)]
  simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (d x) (fun n hn => by
      rw [if_neg]
      intro h'
      apply hn
      have := congrArg (fun e => e x) h'
      simp at this
      exact this.symm), if_pos h]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro n
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp

theorem pderiv_series_at_variable (i x : Fin 2) (f : PowerSeries K) :
    pd i (at1 x f : A2) = at1 x (dz f) * pd i (MvPowerSeries.X x : A2) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_pderiv, coeff_at1_fin_two_eq_ite]
  by_cases hix : i = x
  · subst hix
    rw [show pd i (MvPowerSeries.X i : A2) = 1 from MvPowerSeries.pderiv_X_self, mul_one, coeff_at1_fin_two_eq_ite,
      PowerSeries.coeff_derivative]
    by_cases hd : d = Finsupp.single i (d i)
    · have h2 : d + Finsupp.single i 1 = Finsupp.single i ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) i) := by
        conv_lhs => rw [hd]
        simp
      rw [if_pos h2, if_pos hd, Finsupp.add_apply, Finsupp.single_eq_same]
    · have h2 : ¬ d + Finsupp.single i 1 = Finsupp.single i ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) i) := by
        intro h'
        apply hd
        ext j
        have := congrArg (fun e => e j) h'
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Finsupp.single_apply, Ne.symm hj] at this ⊢
          exact this
      rw [if_neg h2, if_neg hd, zero_mul]
  · rw [show pd i (MvPowerSeries.X x : A2) = 0 from MvPowerSeries.pderiv_X_of_ne (Ne.symm hix), mul_zero,
      map_zero]
    have h2 : ¬ d + Finsupp.single i 1 = Finsupp.single x ((d + Finsupp.single i 1 : Fin 2 →₀ ℕ) x) := by
      intro h'
      have := congrArg (fun e => e i) h'
      simp [Finsupp.single_apply, Ne.symm hix] at this
    rw [if_neg h2, zero_mul]

theorem partialDeriv_inVar_self (x : Fin 2) (f : PowerSeries K) : pd x (at1 x f : A2) = at1 x (dz f) := by
  rw [pderiv_series_at_variable, show pd x (MvPowerSeries.X x : A2) = 1 from MvPowerSeries.pderiv_X_self, mul_one]

theorem partialDeriv_inVar_of_ne {i x : Fin 2} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A2) = 0 := by
  rw [pderiv_series_at_variable, show pd i (MvPowerSeries.X x : A2) = 0 from MvPowerSeries.pderiv_X_of_ne h, mul_zero]

theorem pd_two (i : Fin 2) : MvPowerSeries.pderiv K i (2 : A2) = 0 := by
  rw [show (2 : A2) = ((2 : ℕ) : A2) by norm_num, Derivation.map_natCast]

def Lop (f : A2) : A2 :=
  f * (pd 0 (pd 0 f) - pd 1 (pd 1 f)) - pd 0 f ^ 2 + pd 1 f ^ 2

theorem ring_core {R : Type} [CommRing R] (a b p r p1 r1 p2 r2 h g3 : R)
    (F1a : a ^ 4 * p1 ^ 2 - 4 * a * p1 = 12 * p + 12 * a ^ 2 * p ^ 2 + 4 * a ^ 4 * p ^ 3 -
      (2 * h) * a ^ 2 * (1 + a ^ 2 * p) - g3 * a ^ 4)
    (KoszulLowersPower : a ^ 2 * p2 = 12 * p + 6 * a ^ 2 * p ^ 2 - h * a ^ 2)
    (AutomorphicLevelEquivariance : b ^ 4 * r1 ^ 2 - 4 * b * r1 = 12 * r + 12 * b ^ 2 * r ^ 2 + 4 * b ^ 4 * r ^ 3 -
      (2 * h) * b ^ 2 * (1 + b ^ 2 * r) - g3 * b ^ 4)
    (KoszulImageInIdeal : b ^ 2 * r2 = 12 * r + 6 * b ^ 2 * r ^ 2 - h * b ^ 2) :
    (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) *
      ((2 + 2 * b ^ 2 * (r - p) - 4 * a * b ^ 2 * p1 - a ^ 2 * b ^ 2 * p2) -
        (-2 + 2 * a ^ 2 * (r - p) + 4 * a ^ 2 * b * r1 + a ^ 2 * b ^ 2 * r2)) -
      (2 * a + 2 * a * b ^ 2 * (r - p) - a ^ 2 * b ^ 2 * p1) ^ 2 +
      (-2 * b + 2 * a ^ 2 * b * (r - p) + a ^ 2 * b ^ 2 * r1) ^ 2 =
    (2 * p - 2 * r) * (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) ^ 2 := by
  linear_combination (-b ^ 4) * F1a + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * b ^ 2) * KoszulLowersPower +
    (a ^ 4) * AutomorphicLevelEquivariance + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * a ^ 2) * KoszulImageInIdeal

theorem pderiv_zero_weierstrass_difference (P : PowerSeries K) : pd 0 (wpDiff P) =
    2 * MvPowerSeries.X 0 + 2 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P) -
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz P) := by
  unfold wpDiff
  have s0 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : MvPowerSeries.pderiv K 0 (2 : A2) = 0 := pd_two 0
  have t1 : MvPowerSeries.pderiv K 1 (2 : A2) = 0 := pd_two 1
  simp only [pd, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), s0, s1, n01, n10, t0, t1,
    map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat, pow_one, pow_zero,
    Nat.add_one_sub_one]
  ring

theorem pderiv_one_weierstrass_difference (P : PowerSeries K) : pd 1 (wpDiff P) =
    -2 * MvPowerSeries.X 1 + 2 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * (at1 1 P - at1 0 P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz P) := by
  unfold wpDiff
  have s0 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : MvPowerSeries.pderiv K 0 (2 : A2) = 0 := pd_two 0
  have t1 : MvPowerSeries.pderiv K 1 (2 : A2) = 0 := pd_two 1
  simp only [pd, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), s0, s1, n01, n10, t0, t1,
    map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat, pow_one, pow_zero,
    Nat.add_one_sub_one]
  ring

theorem pderiv_zero_zero_weierstrass_difference (P : PowerSeries K) : pd 0 (pd 0 (wpDiff P)) =
    2 + 2 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P) -
      4 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz P) -
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz (dz P)) := by
  rw [pderiv_zero_weierstrass_difference]
  have s0 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : MvPowerSeries.pderiv K 0 (2 : A2) = 0 := pd_two 0
  have t1 : MvPowerSeries.pderiv K 1 (2 : A2) = 0 := pd_two 1
  simp only [pd, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), s0, s1, n01, n10, t0, t1,
    map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat, pow_one, pow_zero,
    Nat.add_one_sub_one]
  ring

theorem pderiv_one_one_weierstrass_difference (P : PowerSeries K) : pd 1 (pd 1 (wpDiff P)) =
    -2 + 2 * MvPowerSeries.X 0 ^ 2 * (at1 1 P - at1 0 P) +
      4 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * at1 1 (dz P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz (dz P)) := by
  rw [pderiv_one_weierstrass_difference]
  have s0 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : MvPowerSeries.pderiv K 0 (2 : A2) = 0 := pd_two 0
  have t1 : MvPowerSeries.pderiv K 1 (2 : A2) = 0 := pd_two 1
  simp only [pd, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), s0, s1, n01, n10, t0, t1,
    map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat, pow_one, pow_zero,
    Nat.add_one_sub_one]
  ring

theorem Lop_mulD (N : A2) :
    Lop ((MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * N) =
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) ^ 2 * Lop N := by
  unfold Lop
  simp only [pd, Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), mul_one, mul_zero, zero_mul,
    add_zero, zero_add, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one, pow_zero, sub_zero, pd_two, map_zero]
  ring

theorem series_at_variable_const (x : Fin 2) (c : K) : (at1 x (PowerSeries.C c) : A2) = MvPowerSeries.C c := by
  exact PowerSeries.subst_C c

theorem Lop_wpDiff (h8 : WpReduced) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) :
    Lop (wpDiff P) = (2 * at1 0 P - 2 * at1 1 P) * wpDiff P ^ 2 := by
  obtain ⟨hA, hB⟩ := h8 K g2 g3 P hP
  have hX : ∀ x : Fin 2, (at1 x PowerSeries.X : A2) = MvPowerSeries.X x := fun x =>
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)
  have T : ∀ (x : Fin 2) (F : PowerSeries K),
      PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x) F = (at1 x F : A2) :=
    fun x F => (triple_lintegral_eq x F).symm
  have hC : (MvPowerSeries.C g2 : A2) = 2 * MvPowerSeries.C (g2 / 2) := by
    have e : g2 = 2 * (g2 / 2) := by ring
    conv_lhs => rw [e]
    rw [map_mul, map_ofNat]
  have F1 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 4 * (at1 x (dz P)) ^ 2 - 4 * MvPowerSeries.X x * at1 x (dz P) =
      12 * at1 x P + 12 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 + 4 * (MvPowerSeries.X x) ^ 4 * (at1 x P) ^ 3 -
        MvPowerSeries.C g2 * (MvPowerSeries.X x) ^ 2 * (1 + (MvPowerSeries.X x) ^ 2 * at1 x P) -
        MvPowerSeries.C g3 * (MvPowerSeries.X x) ^ 4 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hA
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at this
    simp only [T, hX, series_at_variable_const] at this
    exact this
  have F2 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 2 * at1 x (dz (dz P)) =
      12 * at1 x P + 6 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 -
        MvPowerSeries.C (g2 / 2) * (MvPowerSeries.X x) ^ 2 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hB
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at this
    simp only [T, hX, series_at_variable_const] at this
    exact this
  have F1a := F1 0
  have AutomorphicLevelEquivariance := F1 1
  rw [hC] at F1a AutomorphicLevelEquivariance
  have key := ring_core (MvPowerSeries.X 0 : A2) (MvPowerSeries.X 1) (at1 0 P) (at1 1 P) (at1 0 (dz P))
    (at1 1 (dz P)) (at1 0 (dz (dz P))) (at1 1 (dz (dz P))) (MvPowerSeries.C (g2 / 2)) (MvPowerSeries.C g3)
    (by linear_combination F1a) (F2 0) (by linear_combination AutomorphicLevelEquivariance) (F2 1)
  unfold Lop
  rw [pderiv_zero_zero_weierstrass_difference, pderiv_one_one_weierstrass_difference, pderiv_zero_weierstrass_difference, pderiv_one_weierstrass_difference]
  unfold wpDiff
  linear_combination key

theorem wpDiff_eq (h9 : DqRule) {P : PowerSeries K}
    (hP : ∀ n, Odd n → PowerSeries.coeff n P = 0) :
    wpDiff P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) *
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
  have h := h9 K P hP
  unfold wpDiff
  linear_combination (-(MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 : A2)) * h

theorem D_ne_zero : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : A2) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 2)) h
  have hne : (Finsupp.single (0 : Fin 2) 2) ≠ Finsupp.single 1 2 := by
    intro h'
    have := (Finsupp.single_left_inj two_ne_zero).1 h'
    exact absurd this (by decide)
  simp [MvPowerSeries.coeff_X_pow, hne] at this

theorem ne_zero_of_cc {N : A2} (h : MvPowerSeries.constantCoeff N = 1) : N ≠ 0 := by
  intro h0
  rw [h0, map_zero] at h
  exact zero_ne_one h

theorem Lop_log (h2 : ExpLogDeriv) {N : A2} (hN : MvPowerSeries.constantCoeff N = 1) :
    N ^ 2 * (pd 0 (pd 0 (fLog N)) - pd 1 (pd 1 (fLog N))) = Lop N := by
  have e0 := (h2 K (Fin 2) 0).2 N hN
  have e1 := (h2 K (Fin 2) 1).2 N hN
  have d0 : pd 0 (N * pd 0 (fLog N)) = pd 0 (pd 0 N) := by rw [e0]
  have d1 : pd 1 (N * pd 1 (fLog N)) = pd 1 (pd 1 N) := by rw [e1]
  simp only [pd, Derivation.leibniz, smul_eq_mul] at d0 d1 e0 e1 ⊢
  unfold Lop
  simp only [pd]
  linear_combination N * d0 - MvPowerSeries.pderiv K 0 N * e0 - N * d1 + MvPowerSeries.pderiv K 1 N * e1

theorem evalYZero_eq (h : A2) : ev0 h = MvPowerSeries.substAlgHom Formalism.G.LogP.hb0 h := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

theorem evalFirst_X_one_mul_eq_zero (h : A2) : ev0 (MvPowerSeries.X 1 * h) = 0 := by
  rw [evalYZero_eq, map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X Formalism.G.LogP.hb0]
  simp

theorem fLog_one {ι : Type} : fLog (1 : MvPowerSeries ι K) = 0 := by
  unfold fLog
  rw [sub_self]
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries ι K) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (show PowerSeries.constantCoeff (PowerSeries.log K) = 0 by
    simp [PowerSeries.log])
  rw [hg, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, zero_mul]

end

end Add0

open Add0

theorem AddSigmaLog_of (h2 : ExpLogDeriv) (h3 : ExpLogSubst) (h4 : PrimRules)
    (h5 : WaveUnique) (h6 : WaveKills) (h7 : ParCauchy) (h8 : WpReduced) (h9 : DqRule) :
    AddSigmaLog := by
  intro K _ _ g2 g3 P hP
  have hPodd := hP.2.1
  obtain ⟨f, hf⟩ : ∃ f, f = sigS P := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : MvPowerSeries (Fin 2) K,
      N = 1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P := ⟨_, rfl⟩
  rw [← hf, ← hNdef]
  have hN1 : MvPowerSeries.constantCoeff N = 1 := by simp [hNdef]
  have hNne : N ≠ 0 := ne_zero_of_cc hN1
  obtain ⟨hpr1, -⟩ := h4 K (prim P)
  obtain ⟨hpr1', -⟩ := h4 K P
  have hddf : dz (dz f) = -P := by
    rw [hf, sigS]
    show PowerSeries.derivative K (PowerSeries.derivative K (-prim (prim P))) = -P
    rw [map_neg, map_neg, show PowerSeries.derivative K (prim (prim P)) = prim P from hpr1,
      show PowerSeries.derivative K (prim P) = P from hpr1']
  have hLopN : Lop N = (2 * at1 0 P - 2 * at1 1 P) * N ^ 2 := by
    have e1 := Lop_wpDiff h8 hP
    rw [wpDiff_eq h9 hPodd, ← hNdef, Lop_mulD] at e1
    have hD2 : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : MvPowerSeries (Fin 2) K) ^ 2 ≠ 0 :=
      pow_ne_zero _ D_ne_zero
    apply mul_left_cancel₀ hD2
    rw [e1]
    ring
  have hL : pd 0 (pd 0 (fLog N)) - pd 1 (pd 1 (fLog N)) = 2 * at1 0 P - 2 * at1 1 P := by
    have e2 := Lop_log h2 hN1
    rw [hLopN] at e2
    apply mul_left_cancel₀ (pow_ne_zero 2 hNne)
    rw [e2]
    ring
  have hW := h6 K f
  have hneg : ∀ x : Fin 2, (at1 x (-P) : MvPowerSeries (Fin 2) K) = -at1 x P := fun x => by
    rw [triple_lintegral_eq, map_neg, ← triple_lintegral_eq]
  rw [hddf, hneg, hneg] at hW
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [hf]
    simp only [sigS, map_neg, neg_eq_zero]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, prim, PowerSeries.coeff_mk, if_pos rfl]
  have hf1 : PowerSeries.coeff 1 f = 0 := by
    rw [hf]
    simp only [sigS, map_neg, prim, PowerSeries.coeff_mk, one_ne_zero, if_false, Nat.sub_self, if_true,
      zero_div, neg_zero]
  obtain ⟨hc0, hc1⟩ := h7 K f hf0 hf1
  have hφ : ∀ i, MvPowerSeries.constantCoeff (![(PowerSeries.X : PowerSeries K), 0] i) = 0 := by
    intro i
    fin_cases i
    · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0
      exact PowerSeries.constantCoeff_X
    · simp
  have hevN : ev0 N = 1 := by
    rw [hNdef, show (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * dq P) by ring]
    rw [evalYZero_eq, map_sub, map_one, ← evalYZero_eq, evalFirst_X_one_mul_eq_zero, sub_zero]
  have hevL : ev0 (fLog N) = 0 := by
    have e4 := (h3 K (Fin 2) Unit ![(PowerSeries.X : PowerSeries K), 0] hφ).2 N hN1
    have e5 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] N = 1 := hevN
    unfold ev0
    rw [e4, e5, fLog_one]
  have hpdN : pd 1 N = MvPowerSeries.X 1 *
      (-(MvPowerSeries.X 0 ^ 2 * (2 * dq P + MvPowerSeries.X 1 * pd 1 (dq P)))) := by
    rw [hNdef]
    simp only [pd, map_sub, map_one, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide),
      Derivation.map_one_eq_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat,
      pow_one, Nat.add_one_sub_one]
    ring
  have hevpdL : ev0 (pd 1 (fLog N)) = 0 := by
    have e3 := (h2 K (Fin 2) 1).2 N hN1
    have e6 := congrArg ev0 e3
    rw [hpdN, evalFirst_X_one_mul_eq_zero, evalYZero_eq, map_mul, ← evalYZero_eq, ← evalYZero_eq, hevN, one_mul] at e6
    exact e6
  apply sub_eq_zero.1
  apply h5 K
  · simp only [map_sub]
    linear_combination hW - hL
  · rw [evalYZero_eq, map_sub, ← evalYZero_eq, ← evalYZero_eq, hc0, hevL, sub_zero]
  · rw [show pd 1 (par0 f - fLog N) = pd 1 (par0 f) - pd 1 (fLog N) from map_sub _ _ _, evalYZero_eq, map_sub,
      ← evalYZero_eq, ← evalYZero_eq, hc1, hevpdL, sub_zero]

namespace Add0

section

variable {K : Type} [Field K] [CharZero K]

theorem subst_fExp (h3 : ExpLogSubst) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by
  exact (h3 K Unit (Fin 2) (fun _ => u) (fun _ => hu)).1 f hf

theorem sigS_cc (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  simp only [sigS, map_neg, neg_eq_zero]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, prim, PowerSeries.coeff_mk, if_pos rfl]

theorem subst_sigma (h3 : ExpLogSubst) (P : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u (sigS P)) := by
  have ha : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sigma
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha,
    subst_fExp h3 hu (sigS_cc P)]

theorem subst_sgStar (h3 : ExpLogSubst) (s2 : K) (P : PowerSeries K)
    {u : MvPowerSeries (Fin 2) K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sgStar s2 P) =
      PowerSeries.subst u (sigma P) * fExp (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) := by
  have ha : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sgStar
  have hg : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    simp
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom]
  congr 1
  rw [subst_fExp h3 hu hg]
  congr 1
  rw [← PowerSeries.coe_substAlgHom ha, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, PowerSeries.subst_C]

end

end Add0

theorem AddSigma_of (hL : AddSigmaLog) (h1 : ExpLogRules) (h3 : ExpLogSubst) (h9 : DqRule) :
    AddSigma := by
  intro K _ _ g2 g3 P hP
  have hLog := hL K g2 g3 P hP
  obtain ⟨hadd, -, hexplog⟩ := h1 K (Fin 2)
  have hf0 : PowerSeries.constantCoeff (sigS P) = 0 := Add0.sigS_cc P
  have hcc : ∀ (u : MvPowerSeries (Fin 2) K) (g : PowerSeries K), MvPowerSeries.constantCoeff u = 0 →
      PowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (PowerSeries.subst u g) = 0 := by
    intro u g hu hg
    obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
    have ha := PowerSeries.HasSubst.of_constantCoeff_zero hu
    rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, map_mul,
      hu, zero_mul]
  have hS0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hD0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hX0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have eS : atS (sigma P) = (MvPowerSeries.X 0 + MvPowerSeries.X 1) * fExp (atS (sigS P)) :=
    Add0.subst_sigma h3 P hS0
  have eD : atD (sigma P) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * fExp (atD (sigS P)) :=
    Add0.subst_sigma h3 P hD0
  have e0 : (at1 0 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 0 * fExp (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P (hX0 0)
  have e1 : (at1 1 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * fExp (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P (hX0 1)
  have cS : MvPowerSeries.constantCoeff (atS (sigS P)) = 0 := hcc _ _ hS0 hf0
  have cD : MvPowerSeries.constantCoeff (atD (sigS P)) = 0 := hcc _ _ hD0 hf0
  have c0 : MvPowerSeries.constantCoeff (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 0) hf0
  have c1 : MvPowerSeries.constantCoeff (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 1) hf0
  have hN1 : MvPowerSeries.constantCoeff
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) = 1 := by simp
  obtain ⟨hlog0, hexpN⟩ := hexplog _ hN1
  have hsum : atS (sigS P) + atD (sigS P) = (at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) + fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    unfold par0 at hLog
    linear_combination hLog
  have c00 : MvPowerSeries.constantCoeff (at1 0 (sigS P) + at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c0, add_zero]
  have c11 : MvPowerSeries.constantCoeff (at1 1 (sigS P) + at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c1, add_zero]
  have c0011 : MvPowerSeries.constantCoeff ((at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c00, c11, add_zero]
  have hprod : fExp (atS (sigS P)) * fExp (atD (sigS P)) =
      (fExp (at1 0 (sigS P)) * fExp (at1 0 (sigS P))) * (fExp (at1 1 (sigS P)) * fExp (at1 1 (sigS P))) *
        (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    rw [← hadd _ _ cS cD, hsum, hadd _ _ c0011 hlog0, hadd _ _ c00 c11, hadd _ _ c0 c0, hadd _ _ c1 c1, hexpN]
  rw [eS, eD, e0, e1, Add0.wpDiff_eq h9 hP.2.1]
  linear_combination (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 *
    (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) : MvPowerSeries (Fin 2) K) * hprod

theorem AddSgStar_of (hA : AddSigma) (h1 : ExpLogRules) (h3 : ExpLogSubst) : AddSgStar := by
  intro K _ _ g2 g3 s2 P hP
  have hAP := hA K g2 g3 P hP
  obtain ⟨hadd, -, -⟩ := h1 K (Fin 2)
  have hS0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hD0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hX0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have hq : ∀ u : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) = 0 := fun u hu => by simp [hu]
  have eS : atS (sgStar s2 P) = atS (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hS0
  have eD : atD (sgStar s2 P) = atD (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hD0
  have e0 : (at1 0 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 0 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P (hX0 0)
  have e1 : (at1 1 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 1 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P (hX0 1)
  have q0 := hq _ (hX0 0)
  have q1 := hq _ (hX0 1)
  have q00 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q0, add_zero]
  have q11 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q1, add_zero]
  have hG : fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) =
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2))) *
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2))) := by
    rw [← hadd _ _ (hq _ hS0) (hq _ hD0), ← hadd _ _ q0 q0, ← hadd _ _ q1 q1, ← hadd _ _ q00 q11]
    congr 1
    ring
  rw [eS, eD, e0, e1]
  linear_combination (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2))) * hAP +
    ((at1 0 (sigma P) : MvPowerSeries (Fin 2) K) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P) * hG

end Formalism.L2.Th1.B
