import Mathlib
import GroundTheory.LocalFields.FormalGroups.Basics

namespace GroundTheory.Arith.Abelian

open PowerSeries

noncomputable section

section Poly

variable {A : Type*} [CommRing A]

def zwPoly (W : WeierstrassCurve A) (z w : A) : A :=
  z ^ 3 + W.a₁ * z * w + W.a₂ * z ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * z * w ^ 2 + W.a₆ * w ^ 3 - w

theorem map_zwPoly {B : Type*} [CommRing B] (f : A →+* B) (W : WeierstrassCurve A) (z w : A) :
    f (zwPoly W z w) = zwPoly (W.map f) (f z) (f w) := by
  simp [zwPoly]

end Poly

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def vStep (v : PowerSeries R) : PowerSeries R :=
  1 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X ^ 3 * v ^ 2 + C W.a₄ * X ^ 4 * v ^ 2 +
    C W.a₆ * X ^ 6 * v ^ 3

theorem vStep_sub (f g : PowerSeries R) : vStep W f - vStep W g = X * ((f - g) *
    (C W.a₁ + C W.a₂ * X + (C W.a₃ * X ^ 2 + C W.a₄ * X ^ 3) * (f + g) +
      C W.a₆ * X ^ 5 * (f ^ 2 + f * g + g ^ 2))) := by
  simp only [vStep]; ring

theorem vStep_contract (f g : PowerSeries R) (n : ℕ)
    (h : (n : ℕ∞) ≤ MvPowerSeries.order (f - g)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (vStep W f - vStep W g) := by
  rw [vStep_sub]
  refine le_trans ?_ MvPowerSeries.le_order_mul
  have hX : (1 : ℕ∞) ≤ MvPowerSeries.order (X : PowerSeries R) :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 PowerSeries.constantCoeff_X
  have h2 := le_trans h (le_trans (le_self_add) (MvPowerSeries.le_order_mul (f := f - g)
    (g := C W.a₁ + C W.a₂ * X + (C W.a₃ * X ^ 2 + C W.a₄ * X ^ 3) * (f + g) +
      C W.a₆ * X ^ 5 * (f ^ 2 + f * g + g ^ 2))))
  calc ((n + 1 : ℕ) : ℕ∞) = 1 + (n : ℕ∞) := by push_cast; ring
    _ ≤ _ := add_le_add hX h2

theorem existsUnique_vStep : ∃! v : PowerSeries R, vStep W v = v :=
  GroundTheory.LocalField.FormalGroup.existsUnique_fixedPoint (vStep W) (vStep_contract W)

def formalV : PowerSeries R := (existsUnique_vStep W).exists.choose

theorem vStep_formalV : vStep W (formalV W) = formalV W :=
  (existsUnique_vStep W).exists.choose_spec

theorem eq_formalV {v : PowerSeries R} (h : vStep W v = v) : v = formalV W :=
  (existsUnique_vStep W).unique h (vStep_formalV W)

def formalW : PowerSeries R := X ^ 3 * formalV W

theorem formalW_eq : formalW W = X ^ 3 + C W.a₁ * X * formalW W + C W.a₂ * X ^ 2 * formalW W +
    C W.a₃ * formalW W ^ 2 + C W.a₄ * X * formalW W ^ 2 + C W.a₆ * formalW W ^ 3 := by
  conv_lhs => rw [formalW, ← vStep_formalV]
  simp only [formalW, vStep]; ring

theorem zwPoly_formalW : zwPoly (W.map C) X (formalW W) = 0 := by
  rw [zwPoly, sub_eq_zero]
  conv_rhs => rw [formalW_eq]
  simp

theorem constantCoeff_formalV : constantCoeff (formalV W) = 1 := by
  conv_lhs => rw [← vStep_formalV]
  simp [vStep]

theorem map_formalV {S : Type*} [CommRing S] (f : R →+* S) :
    (formalV W).map f = formalV (W.map f) := by
  refine eq_formalV _ ?_
  conv_rhs => rw [← vStep_formalV]
  simp [vStep]

theorem map_formalW {S : Type*} [CommRing S] (f : R →+* S) :
    (formalW W).map f = formalW (W.map f) := by
  simp [formalW, map_formalV]

theorem coeff_subst_X {σ : Type*} [DecidableEq σ] (i : σ) (f : PowerSeries R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) f) =
      if d = Finsupp.single i (d i) then PowerSeries.coeff (d i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i)]
  simp_rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [finsum_eq_single _ (d i)]
  intro n hn
  rw [if_neg]
  rintro rfl
  simp at hn

def divDiff (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  fun d => PowerSeries.coeff (d 0 + d 1 + 1) f

theorem coeff_divDiff (f : PowerSeries R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (divDiff f) = PowerSeries.coeff (d 0 + d 1 + 1) f := rfl

theorem fin_two_eq_single_one_iff (d : Fin 2 →₀ ℕ) : d = Finsupp.single 1 (d 1) ↔ d 0 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem fin_two_eq_single_zero_iff (d : Fin 2 →₀ ℕ) : d = Finsupp.single 0 (d 0) ↔ d 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem single_le_fin_two_iff (i : Fin 2) (d : Fin 2 →₀ ℕ) : Finsupp.single i 1 ≤ d ↔ 1 ≤ d i := by
  rw [Finsupp.single_le_iff]

theorem X_sub_X_mul_divDiff (f : PowerSeries R) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * divDiff f =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f -
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f := by
  ext d
  rw [sub_mul, map_sub, map_sub, coeff_subst_X, coeff_subst_X, MvPowerSeries.X, MvPowerSeries.X,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
  simp only [single_le_fin_two_iff, fin_two_eq_single_one_iff, fin_two_eq_single_zero_iff,
    coeff_divDiff, Finsupp.tsub_apply, one_mul]
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  · simp [h0, h1]
  · simp [h0, h1.ne', Nat.one_le_iff_ne_zero.2 h1.ne']
  · simp [h1, h0.ne', Nat.one_le_iff_ne_zero.2 h0.ne']
  · simp [h0.ne', h1.ne', Nat.one_le_iff_ne_zero.2 h0.ne', Nat.one_le_iff_ne_zero.2 h1.ne']
    rw [show d 0 + (d 1 - 1) + 1 = d 0 - 1 + d 1 + 1 by omega, sub_self]

theorem map_divDiff {S : Type*} [CommRing S] (φ : R →+* S) (f : PowerSeries R) :
    MvPowerSeries.map φ (divDiff f) = divDiff (PowerSeries.map φ f) := by
  ext d; simp [coeff_divDiff, MvPowerSeries.coeff_map]

theorem constantCoeff_divDiff (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (divDiff f) = PowerSeries.coeff 1 f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_divDiff]; simp

section Secant

variable {A : Type*} [CommRing A] (V : WeierstrassCurve A)

def secantB (l : A) : A := 1 + V.a₂ * l + V.a₄ * l ^ 2 + V.a₆ * l ^ 3

def secantA (l n : A) : A :=
  V.a₁ * l + V.a₂ * n + V.a₃ * l ^ 2 + 2 * V.a₄ * l * n + 3 * V.a₆ * l ^ 2 * n

theorem map_secantB {B : Type*} [CommRing B] (f : A →+* B) (l : A) :
    f (secantB V l) = secantB (V.map f) (f l) := by simp [secantB]

theorem map_secantA {B : Type*} [CommRing B] (f : A →+* B) (l n : A) :
    f (secantA V l n) = secantA (V.map f) (f l) (f n) := by simp [secantA, map_ofNat]

theorem eq_of_zwPoly_eq_zero {z w w' : A} (h : zwPoly V z w = 0) (h' : zwPoly V z w' = 0)
    (hu : IsUnit (1 - (V.a₁ * z + V.a₂ * z ^ 2 + V.a₃ * (w + w') + V.a₄ * z * (w + w') +
      V.a₆ * (w ^ 2 + w * w' + w' ^ 2)))) : w = w' := by
  have e : (w - w') * (1 - (V.a₁ * z + V.a₂ * z ^ 2 + V.a₃ * (w + w') + V.a₄ * z * (w + w') +
      V.a₆ * (w ^ 2 + w * w' + w' ^ 2))) = 0 := by
    simp only [zwPoly] at h h'
    linear_combination (-1 : A) * h + h'
  rw [← sub_eq_zero]
  exact (hu.mul_left_eq_zero).1 e

end Secant

theorem mul_invOfUnit_one {σ : Type*} {φ : MvPowerSeries σ R} (h : MvPowerSeries.constantCoeff φ = 1) :
    φ * MvPowerSeries.invOfUnit φ 1 = 1 :=
  MvPowerSeries.mul_invOfUnit φ 1 (by simp [h])

theorem map_invOfUnit_one {σ : Type*} {S : Type*} [CommRing S] (f : R →+* S)
    {φ : MvPowerSeries σ R} (h : MvPowerSeries.constantCoeff φ = 1) :
    MvPowerSeries.map f (MvPowerSeries.invOfUnit φ 1) =
      MvPowerSeries.invOfUnit (MvPowerSeries.map f φ) 1 := by
  have h1 : MvPowerSeries.map f φ * MvPowerSeries.map f (MvPowerSeries.invOfUnit φ 1) = 1 := by
    rw [← map_mul, mul_invOfUnit_one h, map_one]
  have h2 : MvPowerSeries.map f φ * MvPowerSeries.invOfUnit (MvPowerSeries.map f φ) 1 = 1 :=
    mul_invOfUnit_one (by simp [h])
  calc _ = MvPowerSeries.map f (MvPowerSeries.invOfUnit φ 1) *
        (MvPowerSeries.map f φ * MvPowerSeries.invOfUnit (MvPowerSeries.map f φ) 1) := by
        rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, mul_comm _ (MvPowerSeries.map f φ), h1, one_mul]

def wAt {τ : Type*} (u : MvPowerSeries τ R) : MvPowerSeries τ R :=
  PowerSeries.subst u (formalW W)

theorem zwPoly_wAt {τ : Type*} {u : MvPowerSeries τ R} (hu : MvPowerSeries.constantCoeff u = 0) :
    zwPoly (W.map MvPowerSeries.C) u (wAt W u) = 0 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  have := congrArg (PowerSeries.substAlgHom (R := R) hs) (zwPoly_formalW W)
  rw [map_zero] at this
  rw [← this]
  simp only [zwPoly, map_add, map_sub, map_mul, map_pow]
  simp [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, wAt]

theorem constantCoeff_wAt {τ : Type*} {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) : MvPowerSeries.constantCoeff (wAt W u) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hu _ (by simp [formalW])

theorem map_wAt {τ : Type*} {S : Type*} [CommRing S] (f : R →+* S) {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    MvPowerSeries.map f (wAt W u) = wAt (W.map f) (MvPowerSeries.map f u) := by
  rw [wAt, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hu), map_formalW, wAt]

def addSlope : MvPowerSeries (Fin 2) R := divDiff (formalW W)

def addIntercept : MvPowerSeries (Fin 2) R :=
  wAt W (MvPowerSeries.X 0) - addSlope W * MvPowerSeries.X 0

def thirdZ : MvPowerSeries (Fin 2) R :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 -
    secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W) *
      MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1

def thirdW : MvPowerSeries (Fin 2) R := addSlope W * thirdZ W + addIntercept W

def negDen : MvPowerSeries (Fin 2) R :=
  1 - MvPowerSeries.C W.a₁ * thirdZ W - MvPowerSeries.C W.a₃ * thirdW W

def addSeries : MvPowerSeries (Fin 2) R :=
  -thirdZ W * MvPowerSeries.invOfUnit (negDen W) 1

theorem constantCoeff_formalW : PowerSeries.constantCoeff (formalW W) = 0 := by simp [formalW]

theorem coeff_one_formalW : PowerSeries.coeff 1 (formalW W) = 0 := by
  rw [formalW, PowerSeries.coeff_X_pow_mul']; simp

theorem constantCoeff_addSlope : MvPowerSeries.constantCoeff (addSlope W) = 0 := by
  rw [addSlope, constantCoeff_divDiff, coeff_one_formalW]

theorem constantCoeff_addIntercept : MvPowerSeries.constantCoeff (addIntercept W) = 0 := by
  simp [addIntercept, constantCoeff_wAt W (MvPowerSeries.constantCoeff_X (R := R) (0 : Fin 2))]

theorem constantCoeff_secantB :
    MvPowerSeries.constantCoeff (secantB (W.map MvPowerSeries.C) (addSlope W)) = 1 := by
  simp [secantB, constantCoeff_addSlope]

theorem constantCoeff_secantA :
    MvPowerSeries.constantCoeff (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W))
      = 0 := by
  simp [secantA, constantCoeff_addSlope, constantCoeff_addIntercept]

theorem constantCoeff_thirdZ : MvPowerSeries.constantCoeff (thirdZ W) = 0 := by
  simp [thirdZ, constantCoeff_secantA]

theorem constantCoeff_thirdW : MvPowerSeries.constantCoeff (thirdW W) = 0 := by
  simp [thirdW, constantCoeff_thirdZ, constantCoeff_addIntercept]

theorem constantCoeff_negDen : MvPowerSeries.constantCoeff (negDen W) = 1 := by
  simp [negDen, constantCoeff_thirdZ, constantCoeff_thirdW]

theorem constantCoeff_addSeries : MvPowerSeries.constantCoeff (addSeries W) = 0 := by
  simp [addSeries, constantCoeff_thirdZ]

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem map_addSlope : MvPowerSeries.map f (addSlope W) = addSlope (W.map f) := by
  rw [addSlope, map_divDiff, map_formalW, addSlope]

theorem map_addIntercept : MvPowerSeries.map f (addIntercept W) = addIntercept (W.map f) := by
  rw [addIntercept, map_sub, map_mul, map_wAt W f (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.map_X, map_addSlope, addIntercept]

theorem map_C_comp : (W.map MvPowerSeries.C).map (MvPowerSeries.map (σ := Fin 2) f) =
    (W.map f).map MvPowerSeries.C := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext a : 1
  simp

theorem map_thirdZ : MvPowerSeries.map f (thirdZ W) = thirdZ (W.map f) := by
  rw [thirdZ, map_sub, map_sub, map_neg, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_X,
    map_invOfUnit_one f (constantCoeff_secantB W), map_secantA, map_secantB, map_C_comp,
    map_addSlope, map_addIntercept, thirdZ]

theorem map_thirdW : MvPowerSeries.map f (thirdW W) = thirdW (W.map f) := by
  rw [thirdW, map_add, map_mul, map_addSlope, map_thirdZ, map_addIntercept, thirdW]

theorem map_negDen : MvPowerSeries.map f (negDen W) = negDen (W.map f) := by
  simp [negDen, map_thirdZ, map_thirdW, MvPowerSeries.map_C]

theorem map_addSeries : MvPowerSeries.map f (addSeries W) = addSeries (W.map f) := by
  rw [addSeries, map_mul, map_neg, map_invOfUnit_one f (constantCoeff_negDen W), map_thirdZ,
    map_negDen, addSeries]

end Map

section LowDegree

variable {τ : Type*}

theorem le_order_add_of_le {n : ℕ∞} {f g : MvPowerSeries τ R} (hf : n ≤ MvPowerSeries.order f)
    (hg : n ≤ MvPowerSeries.order g) : n ≤ MvPowerSeries.order (f + g) :=
  le_trans (le_min hf hg) MvPowerSeries.min_order_le_add

theorem le_order_mul_of_le_left {n : ℕ∞} {f : MvPowerSeries τ R} (g : MvPowerSeries τ R)
    (hf : n ≤ MvPowerSeries.order f) : n ≤ MvPowerSeries.order (f * g) :=
  le_trans (le_trans hf le_self_add) MvPowerSeries.le_order_mul

theorem le_order_mul_of_le {m n : ℕ∞} {f g : MvPowerSeries τ R} (hf : m ≤ MvPowerSeries.order f)
    (hg : n ≤ MvPowerSeries.order g) : m + n ≤ MvPowerSeries.order (f * g) :=
  le_trans (add_le_add hf hg) MvPowerSeries.le_order_mul

theorem degree_fin_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem two_le_order_addSlope : (2 : ℕ∞) ≤ MvPowerSeries.order (addSlope W) := by
  refine MvPowerSeries.nat_le_order fun d hd => ?_
  have hd2 : d 0 + d 1 < 2 := by rw [degree_fin_two] at hd; exact_mod_cast hd
  rw [addSlope, coeff_divDiff, formalW, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem two_le_order_wAt_X (i : Fin 2) :
    (2 : ℕ∞) ≤ MvPowerSeries.order (wAt W (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) := by
  refine MvPowerSeries.nat_le_order fun d hd => ?_
  have hd2 : d.degree < 2 := by exact_mod_cast hd
  rw [wAt, coeff_subst_X]
  split_ifs with h
  · have : d i ≤ d.degree := by
      rw [degree_fin_two]; fin_cases i <;> simp
    rw [formalW, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  · rfl

theorem two_le_order_addIntercept : (2 : ℕ∞) ≤ MvPowerSeries.order (addIntercept W) := by
  rw [addIntercept, sub_eq_add_neg]
  refine le_order_add_of_le (two_le_order_wAt_X W 0) ?_
  rw [MvPowerSeries.order_neg]
  exact le_order_mul_of_le_left _ (two_le_order_addSlope W)

theorem two_le_order_secantA :
    (2 : ℕ∞) ≤ MvPowerSeries.order (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W)) := by
  have e : secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W) =
      addSlope W * (MvPowerSeries.C W.a₁ + MvPowerSeries.C W.a₃ * addSlope W) +
      addIntercept W * (MvPowerSeries.C W.a₂ + 2 * MvPowerSeries.C W.a₄ * addSlope W +
        3 * MvPowerSeries.C W.a₆ * addSlope W ^ 2) := by
    simp only [secantA, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    ring
  rw [e]
  exact le_order_add_of_le (le_order_mul_of_le_left _ (two_le_order_addSlope W))
    (le_order_mul_of_le_left _ (two_le_order_addIntercept W))

theorem two_le_order_thirdZ_add :
    (2 : ℕ∞) ≤ MvPowerSeries.order (thirdZ W - (-MvPowerSeries.X 0 - MvPowerSeries.X 1)) := by
  have e : thirdZ W - (-MvPowerSeries.X 0 - MvPowerSeries.X 1) =
      -(secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W) *
        MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) := by
    rw [thirdZ]; ring
  rw [e, MvPowerSeries.order_neg]
  exact le_order_mul_of_le_left _ (two_le_order_secantA W)

theorem one_le_order_X_add_X :
    (1 : ℕ∞) ≤ MvPowerSeries.order (MvPowerSeries.X 0 + MvPowerSeries.X 1 :
      MvPowerSeries (Fin 2) R) :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 (by simp)

theorem two_le_order_addSeries_sub :
    (2 : ℕ∞) ≤ MvPowerSeries.order (addSeries W - (MvPowerSeries.X 0 + MvPowerSeries.X 1)) := by
  set c := MvPowerSeries.invOfUnit (negDen W) 1
  have e : addSeries W - (MvPowerSeries.X 0 + MvPowerSeries.X 1) =
      -(thirdZ W - (-MvPowerSeries.X 0 - MvPowerSeries.X 1)) * c +
        (MvPowerSeries.X 0 + MvPowerSeries.X 1) * (c - 1) := by
    rw [addSeries]; ring
  have hc : (1 : ℕ∞) ≤ MvPowerSeries.order (c - 1) :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 (by simp [c])
  rw [e]
  refine le_order_add_of_le ?_ ?_
  · rw [neg_mul, MvPowerSeries.order_neg]
    exact le_order_mul_of_le_left _ (two_le_order_thirdZ_add W)
  · calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := le_order_mul_of_le one_le_order_X_add_X hc

theorem coeff_single_subst_pair [DecidableEq τ] {G : MvPowerSeries (Fin 2) R} {c₀ c₁ : R}
    (hG : (2 : ℕ∞) ≤ MvPowerSeries.order (G - (MvPowerSeries.C c₀ * MvPowerSeries.X 0 +
      MvPowerSeries.C c₁ * MvPowerSeries.X 1)))
    {a b : MvPowerSeries τ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (i : τ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst ![a, b] G) =
      c₀ * MvPowerSeries.coeff (Finsupp.single i 1) a +
        c₁ * MvPowerSeries.coeff (Finsupp.single i 1) b := by
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair ha hb
  set H := G - (MvPowerSeries.C c₀ * MvPowerSeries.X 0 + MvPowerSeries.C c₁ * MvPowerSeries.X 1)
  have hGH : G = MvPowerSeries.C c₀ * MvPowerSeries.X 0 + MvPowerSeries.C c₁ * MvPowerSeries.X 1 +
      H := by simp [H]
  have h2 : (2 : ℕ∞) ≤ MvPowerSeries.order (MvPowerSeries.subst ![a, b] H) := by
    have := GroundTheory.LocalField.FormalGroup.le_order_subst_sub_subst (f := H) (g := 0) hab
      (fun j => by fin_cases j <;> simp [ha, hb]) (by simpa using hG)
    rwa [← MvPowerSeries.subst_sub hab, sub_zero] at this
  rw [hGH, ← MvPowerSeries.coe_substAlgHom hab]
  simp only [map_add, map_mul, MvPowerSeries.coe_substAlgHom hab, MvPowerSeries.subst_X hab,
    MvPowerSeries.subst_C]
  rw [MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by simp) h2), add_zero,
    MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  simp

end LowDegree

theorem wAt_X_zero_eq : wAt W (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) =
    addSlope W * MvPowerSeries.X 0 + addIntercept W := by
  rw [addIntercept]; ring

theorem wAt_X_one_eq : wAt W (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) =
    addSlope W * MvPowerSeries.X 1 + addIntercept W := by
  have := X_sub_X_mul_divDiff (formalW W)
  simp only [wAt, addIntercept, addSlope]
  linear_combination (-1 : MvPowerSeries (Fin 2) R) * this

def formalG : PowerSeries R := X ^ 2 * formalV W

theorem formalW_eq_X_mul : formalW W = X * formalG W := by
  rw [formalW, formalG]; ring

def gAt {τ : Type*} (u : MvPowerSeries τ R) : MvPowerSeries τ R :=
  PowerSeries.subst u (formalG W)

theorem wAt_eq_mul_gAt {τ : Type*} {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) : wAt W u = u * gAt W u := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [wAt, gAt, formalW_eq_X_mul, ← PowerSeries.coe_substAlgHom hs, map_mul,
    PowerSeries.substAlgHom_X]

theorem isUnit_subst_formalV {τ : Type*} {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) : IsUnit (PowerSeries.subst u (formalV W)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  have h1 : IsUnit (formalV W) := by
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    rw [show MvPowerSeries.constantCoeff (formalV W) = 1 from constantCoeff_formalV W]
    exact isUnit_one
  rw [← PowerSeries.coe_substAlgHom hs]
  exact h1.map _

theorem wAt_eq_pow_mul {τ : Type*} {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    wAt W u = u ^ 3 * PowerSeries.subst u (formalV W) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [wAt, formalW, ← PowerSeries.coe_substAlgHom hs, map_mul, map_pow, PowerSeries.substAlgHom_X]

theorem wAt_ne_zero [IsDomain R] {τ : Type*} {u : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hu0 : u ≠ 0) : wAt W u ≠ 0 := by
  rw [wAt_eq_pow_mul W hu]
  exact mul_ne_zero (pow_ne_zero _ hu0) (isUnit_subst_formalV W hu).ne_zero

theorem gAt_X_one_sub_gAt_X_zero :
    gAt W (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) - gAt W (MvPowerSeries.X 0) =
      (MvPowerSeries.X 1 - MvPowerSeries.X 0) * divDiff (formalG W) :=
  (X_sub_X_mul_divDiff (formalG W)).symm

theorem two_le_order_divDiff_formalG :
    (2 : ℕ∞) ≤ MvPowerSeries.order (divDiff (formalG W) -
      (MvPowerSeries.C 1 * MvPowerSeries.X 0 + MvPowerSeries.C 1 * MvPowerSeries.X 1)) := by
  refine MvPowerSeries.nat_le_order fun d hd => ?_
  have hd2 : d 0 + d 1 < 2 := by rw [degree_fin_two] at hd; exact_mod_cast hd
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℕ, d = Finsupp.single 0 p + Finsupp.single 1 q :=
    ⟨d 0, d 1, by ext i; fin_cases i <;> simp⟩
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, ne_eq, zero_ne_one,
    not_false_eq_true, Finsupp.single_eq_of_ne, add_zero, one_ne_zero, zero_add] at hd2
  have hp : p < 2 := by omega
  have hq : q < 2 := by omega
  interval_cases p <;> interval_cases q <;>
    simp_all [coeff_divDiff, constantCoeff_divDiff, formalG, PowerSeries.coeff_X_pow_mul', MvPowerSeries.coeff_X,
      constantCoeff_formalV, Ne.symm h01]

end

end GroundTheory.Arith.Abelian
