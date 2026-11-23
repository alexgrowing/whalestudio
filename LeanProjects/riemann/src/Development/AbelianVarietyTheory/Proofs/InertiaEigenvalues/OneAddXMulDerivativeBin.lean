import Mathlib

noncomputable section

open PowerSeries

namespace GlobalTheory.CycFr

open PowerSeries in
private theorem algHom_coe_polynomial_eq_aeval {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (p : Polynomial O) : f (p : O⟦X⟧) = Polynomial.aeval (f X) p := by
  have hfp : f.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (f X) :=
    Polynomial.algHom_ext (by simp)
  have := DFunLike.congr_fun hfp p
  simpa using this

open PowerSeries in
private theorem X_pow_dvd_algHom_sub_aeval_trunc {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (a : O⟦X⟧) (n : ℕ) :
    (X : O⟦X⟧) ^ n ∣ f a - Polynomial.aeval (f X) (trunc n a) := by
  obtain ⟨s, hs⟩ : ∃ s : O⟦X⟧, a = X ^ n * s + (trunc n a : O⟦X⟧) := ⟨_, eq_X_pow_mul_shift_add_trunc n a⟩
  rw [← algHom_coe_polynomial_eq_aeval]
  have hdiff : f a - f ↑(trunc n a) = f X ^ n * f s := by
    calc f a - f ↑(trunc n a) = f (X ^ n * s + ↑(trunc n a)) - f ↑(trunc n a) := by rw [← hs]
      _ = f X ^ n * f s := by rw [map_add, map_mul, map_pow, add_sub_cancel_right]
  rw [hdiff]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf n) _

open PowerSeries in

theorem _root_.GlobalTheory.CycFr.algHom_ext_X {O : Type} [CommRing O] (f g : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (h : f X = g X) : f = g := by
  ext a : 1
  refine PowerSeries.ext fun n => ?_
  have h1 := X_pow_dvd_algHom_sub_aeval_trunc f hf a (n + 1)
  have h2 := X_pow_dvd_algHom_sub_aeval_trunc g (h ▸ hf) a (n + 1)
  rw [← h] at h2
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := X_pow_dvd_iff.mp h3 n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at this

open PowerSeries in
theorem _root_.GlobalTheory.CycFr.algHom_C {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (f : O⟦X⟧ →ₐ[O] B) (c : O) :
    f (C c) = algebraMap O B c := by
  have hc : (C c : O⟦X⟧) = algebraMap O O⟦X⟧ c := by simp
  rw [hc, f.commutes]

open PowerSeries in

theorem _root_.GlobalTheory.CycFr.constantCoeff_algHom {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (a : O⟦X⟧) : constantCoeff (f a) = constantCoeff a := by
  obtain ⟨s, hs⟩ : ∃ s, a = s * X + C (constantCoeff a) := ⟨_, eq_shift_mul_X_add_const a⟩
  have h0 : constantCoeff (f X) = 0 := X_dvd_iff.mp hf
  calc constantCoeff (f a) = constantCoeff (f (s * X + C (constantCoeff a))) := by rw [← hs]
    _ = constantCoeff a := by
      rw [map_add, map_mul, _root_.GlobalTheory.CycFr.algHom_C, map_add, map_mul, h0, mul_zero,
        zero_add]
      simp

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

abbrev bin (c : ℤ_[l]) : O⟦X⟧ := binomialSeries O c

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
theorem _root_.GlobalTheory.CycFr.hasSubst_bin (c : ℤ_[l]) : HasSubst (_root_.GlobalTheory.CycFr.bin O c - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, binomialSeries_constantCoeff, map_one, sub_self])

def act (c : ℤ_[l]) : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom (hasSubst_bin O c)

def lvl (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, ((1 + X : O⟦X⟧) ^ l ^ k) ^ i

variable {O}

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.act_apply (c : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c a = a.subst (_root_.GlobalTheory.CycFr.bin O c - 1) := by
  rw [_root_.GlobalTheory.CycFr.act, coe_substAlgHom]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.act_X (c : ℤ_[l]) : _root_.GlobalTheory.CycFr.act O c X = _root_.GlobalTheory.CycFr.bin O c - 1 := by
  rw [_root_.GlobalTheory.CycFr.act_apply, subst_X (_root_.GlobalTheory.CycFr.hasSubst_bin O c)]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.act_one_add_X (c : ℤ_[l]) : _root_.GlobalTheory.CycFr.act O c (1 + X) = _root_.GlobalTheory.CycFr.bin O c := by
  rw [map_add, map_one, _root_.GlobalTheory.CycFr.act_X]
  ring

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.act_C (c : ℤ_[l]) (x : O) : _root_.GlobalTheory.CycFr.act O c (C x) = C x := by
  rw [_root_.GlobalTheory.CycFr.algHom_C]
  simp

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.X_dvd_act_X (c : ℤ_[l]) : (X : O⟦X⟧) ∣ _root_.GlobalTheory.CycFr.act O c X := by
  rw [X_dvd_iff, _root_.GlobalTheory.CycFr.act_X, map_sub, binomialSeries_constantCoeff,
    map_one, sub_self]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.constantCoeff_act (c : ℤ_[l]) (a : O⟦X⟧) : constantCoeff (_root_.GlobalTheory.CycFr.act O c a) = constantCoeff a :=
  _root_.GlobalTheory.CycFr.constantCoeff_algHom _ (_root_.GlobalTheory.CycFr.X_dvd_act_X c) a

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.bin_nat (d : ℕ) : _root_.GlobalTheory.CycFr.bin O (d : ℤ_[l]) = (1 + X) ^ d :=
  binomialSeries_nat d

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.bin_one : _root_.GlobalTheory.CycFr.bin O (1 : ℤ_[l]) = 1 + X := by
  have h := _root_.GlobalTheory.CycFr.bin_nat (O := O) (l := l) 1
  rwa [Nat.cast_one, pow_one] at h

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.coeff_one_act_X (c : ℤ_[l]) : coeff 1 (_root_.GlobalTheory.CycFr.act O c X) = algebraMap ℤ_[l] O c := by
  rw [_root_.GlobalTheory.CycFr.act_X, map_sub, binomialSeries_coeff, Ring.choose_one_right,
    coeff_one, Algebra.smul_def, mul_one]
  simp

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in

theorem _root_.GlobalTheory.CycFr.exists_act_X (c : ℤ_[l]) :
    ∃ v : O⟦X⟧, _root_.GlobalTheory.CycFr.act O c X = X * v ∧ constantCoeff v = algebraMap ℤ_[l] O c := by
  refine ⟨mk fun p => coeff (p + 1) (_root_.GlobalTheory.CycFr.act O c X), ?_, ?_⟩
  · have h := sub_const_eq_X_mul_shift (_root_.GlobalTheory.CycFr.act O c X)
    rwa [_root_.GlobalTheory.CycFr.constantCoeff_act, constantCoeff_X, map_zero,
      sub_zero] at h
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add,
      _root_.GlobalTheory.CycFr.coeff_one_act_X]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.derivative_bin (c : ℤ_[l]) :
    derivative O (_root_.GlobalTheory.CycFr.bin O c) = C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O (c - 1) := by
  ext n
  have key : ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = c * Ring.choose (c - 1) n := by
    have h := Ring.choose_smul_choose c (n := n + 1) (k := 1) (by omega)
    simpa [Ring.choose_one_right, nsmul_eq_mul] using h
  rw [coeff_derivative, coeff_C_mul, binomialSeries_coeff, binomialSeries_coeff, Algebra.smul_def,
    Algebra.smul_def, mul_one, mul_one, ← map_mul, ← key, map_mul, mul_comm]
  simp

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
private theorem one_add_X_mul_bin_sub_one_eq_bin (c : ℤ_[l]) :
    (1 + X : O⟦X⟧) * _root_.GlobalTheory.CycFr.bin O (c - 1) = _root_.GlobalTheory.CycFr.bin O c := by
  have h : _root_.GlobalTheory.CycFr.bin O c =
      _root_.GlobalTheory.CycFr.bin O (c - 1) * _root_.GlobalTheory.CycFr.bin O (1 : ℤ_[l]) := by
    simp only [_root_.GlobalTheory.CycFr.bin, ← binomialSeries_add, sub_add_cancel]
  rw [h, _root_.GlobalTheory.CycFr.bin_one, mul_comm]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
theorem _root_.GlobalTheory.CycFr.one_add_X_mul_derivative_bin (c : ℤ_[l]) :
    (1 + X : O⟦X⟧) * derivative O (_root_.GlobalTheory.CycFr.bin O c) =
      C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O c := by
  rw [_root_.GlobalTheory.CycFr.derivative_bin, mul_left_comm,
    one_add_X_mul_bin_sub_one_eq_bin]

variable [IsDomain O] [CharZero O]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
private theorem eq_of_one_add_X_mul_derivative_eq_C_mul {F H : O⟦X⟧} (a : O)
    (hF : (1 + X) * derivative O F = C a * F) (hH : (1 + X) * derivative O H = C a * H)
    (h0 : constantCoeff F = constantCoeff H) : F = H := by
  have hD : (1 + X) * derivative O (F - H) = C a * (F - H) := by
    rw [map_sub, mul_sub, mul_sub, hF, hH]
  have hD0 : coeff 0 (F - H) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, h0, sub_self]
  have key : ∀ n, coeff n (F - H) = 0 ∧ coeff n (derivative O (F - H)) = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨hD0, ?_⟩
      have h := congrArg (coeff 0) hD
      rwa [add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero, coeff_C_mul, hD0,
        mul_zero] at h
    | succ m ih =>
      have h1 : coeff (m + 1) (F - H) = 0 := by
        have h := ih.2
        rw [coeff_derivative] at h
        exact (mul_eq_zero.mp h).resolve_right (Nat.cast_add_one_ne_zero m)
      refine ⟨h1, ?_⟩
      have h := congrArg (coeff (m + 1)) hD
      rwa [add_mul, one_mul, map_add, coeff_succ_X_mul, ih.2, add_zero, coeff_C_mul, h1,
        mul_zero] at h
  ext n
  have h := (key n).1
  rwa [map_sub, sub_eq_zero] at h

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_bin (c d : ℤ_[l]) :
    _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d) =
      _root_.GlobalTheory.CycFr.bin O (c * d) := by
  have hG : derivative O (_root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d)) =
      _root_.GlobalTheory.CycFr.act O c (derivative O (_root_.GlobalTheory.CycFr.bin O d)) *
        derivative O (_root_.GlobalTheory.CycFr.bin O c) := by
    rw [_root_.GlobalTheory.CycFr.act_apply, _root_.GlobalTheory.CycFr.act_apply,
      derivative_subst (_root_.GlobalTheory.CycFr.hasSubst_bin O c), map_sub,
      Derivation.map_one_eq_zero, sub_zero]
  have h1 : _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d) =
      _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O (d - 1)) *
        _root_.GlobalTheory.CycFr.bin O c := by
    rw [← one_add_X_mul_bin_sub_one_eq_bin d, map_mul,
      _root_.GlobalTheory.CycFr.act_one_add_X, mul_comm]
  refine eq_of_one_add_X_mul_derivative_eq_C_mul (algebraMap ℤ_[l] O (c * d)) ?_
    (_root_.GlobalTheory.CycFr.one_add_X_mul_derivative_bin (c * d)) ?_
  · rw [hG, _root_.GlobalTheory.CycFr.derivative_bin, _root_.GlobalTheory.CycFr.derivative_bin, h1,
      ← one_add_X_mul_bin_sub_one_eq_bin c]
    simp only [map_mul, _root_.GlobalTheory.CycFr.act_C]
    ring
  · rw [_root_.GlobalTheory.CycFr.constantCoeff_act, binomialSeries_constantCoeff,
      binomialSeries_constantCoeff]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_mul (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O (c * d) a = _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) := by
  rw [_root_.GlobalTheory.CycFr.act_apply, _root_.GlobalTheory.CycFr.act_apply,
    _root_.GlobalTheory.CycFr.act_apply,
    subst_comp_subst_apply (_root_.GlobalTheory.CycFr.hasSubst_bin O d)
      (_root_.GlobalTheory.CycFr.hasSubst_bin O c)]
  congr 1
  rw [← _root_.GlobalTheory.CycFr.act_apply, map_sub, map_one,
    _root_.GlobalTheory.CycFr.act_bin]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_comm (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) = _root_.GlobalTheory.CycFr.act O d (_root_.GlobalTheory.CycFr.act O c a) := by
  rw [← _root_.GlobalTheory.CycFr.act_mul, ← _root_.GlobalTheory.CycFr.act_mul, mul_comm]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_one (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O (1 : ℤ_[l]) a = a := by
  have h : _root_.GlobalTheory.CycFr.act O (1 : ℤ_[l]) = AlgHom.id O O⟦X⟧ :=
    _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (_root_.GlobalTheory.CycFr.X_dvd_act_X 1)
      (by rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.bin_one,
        add_sub_cancel_left, AlgHom.id_apply])
  rw [h, AlgHom.id_apply]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_nat_X (d : ℕ) : _root_.GlobalTheory.CycFr.act O (d : ℤ_[l]) X = (1 + X) ^ d - 1 := by
  rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.bin_nat]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.mul_lvl (k : ℕ) :
    ((1 + X : O⟦X⟧) ^ l ^ k - 1) * _root_.GlobalTheory.CycFr.lvl l O k = (1 + X) ^ l ^ (k + 1) - 1 := by
  rw [_root_.GlobalTheory.CycFr.lvl, mul_comm, geom_sum_mul, ← pow_mul, ← pow_succ]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [IsDomain O] [CharZero O] in
theorem _root_.GlobalTheory.CycFr.act_l_pow_lvl (k : ℕ) : _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) (_root_.GlobalTheory.CycFr.lvl l O 0) = _root_.GlobalTheory.CycFr.lvl l O k := by
  have hb : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k) = (1 + X) ^ l ^ k := by
    rw [← Nat.cast_pow, _root_.GlobalTheory.CycFr.bin_nat]
  rw [_root_.GlobalTheory.CycFr.lvl, _root_.GlobalTheory.CycFr.lvl, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, pow_zero, pow_one, _root_.GlobalTheory.CycFr.act_one_add_X, hb]

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in

theorem _root_.GlobalTheory.CycFr.dvd_bin_sub (k : ℕ) (c d : ℤ_[l]) (h : (l : ℤ_[l]) ^ k ∣ c - d) :
    (1 + X : O⟦X⟧) ^ l ^ k - 1 ∣ _root_.GlobalTheory.CycFr.bin O c - _root_.GlobalTheory.CycFr.bin O d := by
  obtain ⟨e, he⟩ := h
  have hc : c = d + (l : ℤ_[l]) ^ k * e := by rw [← he]; ring
  have hb : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k) = (1 + X) ^ l ^ k := by
    rw [← Nat.cast_pow, _root_.GlobalTheory.CycFr.bin_nat]
  obtain ⟨v, hv⟩ : (X : O⟦X⟧) ∣ _root_.GlobalTheory.CycFr.bin O e - 1 :=
    X_dvd_iff.mpr (by rw [map_sub, binomialSeries_constantCoeff, map_one, sub_self])
  have h1 : _root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k * e) - 1 =
      ((1 + X) ^ l ^ k - 1) * _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) v := by
    rw [← _root_.GlobalTheory.CycFr.act_bin, ← hb,
      ← _root_.GlobalTheory.CycFr.act_X, ← map_mul, ← hv, map_sub, map_one]
  have h2 : _root_.GlobalTheory.CycFr.bin O c - _root_.GlobalTheory.CycFr.bin O d =
      _root_.GlobalTheory.CycFr.bin O d *
        (_root_.GlobalTheory.CycFr.bin O ((l : ℤ_[l]) ^ k * e) - 1) := by
    rw [hc]
    simp only [_root_.GlobalTheory.CycFr.bin, binomialSeries_add]
    ring
  rw [h2, h1]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O] in

theorem _root_.GlobalTheory.CycFr.dvd_algHom_sub [IsNoetherianRing O] (f g : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (hg : (X : O⟦X⟧) ∣ g X) (h : O⟦X⟧) (hh : h ∣ f X - g X) (a : O⟦X⟧) : h ∣ f a - g a := by
  have hX : Ideal.span {(X : O⟦X⟧)} ≤ (⊥ : Ideal O⟦X⟧).jacobson := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_jacobson_bot]
    intro y
    rw [isUnit_iff_constantCoeff]
    simp
  have hH := IsHausdorff.of_le_jacobson (Ideal.span {(X : O⟦X⟧)}) (O⟦X⟧ ⧸ Ideal.span {h}) hX
  have key : (Submodule.Quotient.mk (f a - g a) : O⟦X⟧ ⧸ Ideal.span {h}) = 0 := by
    refine hH.haus _ fun n => ?_
    rw [SModEq.zero]
    obtain ⟨r, hr⟩ := X_pow_dvd_algHom_sub_aeval_trunc f hf a n
    obtain ⟨s, hs⟩ := X_pow_dvd_algHom_sub_aeval_trunc g hg a n
    have hp : h ∣ Polynomial.aeval (f X) (trunc n a) - Polynomial.aeval (g X) (trunc n a) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.eval₂_eq_eval_map]
      exact hh.trans (Polynomial.sub_dvd_eval_sub _ _ _)
    obtain ⟨q, hq⟩ := hp
    have he : f a - g a = X ^ n * (r - s) + h * q := by
      rw [mul_sub, ← hr, ← hs, ← hq]
      ring
    have hm : (Submodule.Quotient.mk (f a - g a) : O⟦X⟧ ⧸ Ideal.span {h}) =
        (X ^ n * (r - s)) • Submodule.Quotient.mk 1 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.eq, he,
        add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)
    rw [hm]
    exact Submodule.smul_mem_smul
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self X) n))
      Submodule.mem_top
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at key
  exact key

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in

theorem _root_.GlobalTheory.CycFr.dvd_act_sub [IsNoetherianRing O] (k : ℕ) (c d : ℤ_[l]) (h : (l : ℤ_[l]) ^ k ∣ c - d)
    (a : O⟦X⟧) : (1 + X : O⟦X⟧) ^ l ^ k - 1 ∣ _root_.GlobalTheory.CycFr.act O c a - _root_.GlobalTheory.CycFr.act O d a := by
  refine _root_.GlobalTheory.CycFr.dvd_algHom_sub _ _ (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
    (_root_.GlobalTheory.CycFr.X_dvd_act_X d) _ ?_ a
  rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.act_X,
    sub_sub_sub_cancel_right]
  exact _root_.GlobalTheory.CycFr.dvd_bin_sub k c d h

open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O] in

theorem _root_.GlobalTheory.CycFr.dvd_sub_C_of_shift (x : O) (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C x) (a : O⟦X⟧) :
    X - C x ∣ a - C (constantCoeff (σ a)) := by
  have hC : ∀ y : O, (C y : O⟦X⟧) = algebraMap O O⟦X⟧ y := fun y => by simp
  have hinv : σ.symm X = X - C x := by
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply, map_sub, hσ, hC, AlgEquiv.commutes]
    ring
  have hs := congrArg σ.symm (sub_const_eq_X_mul_shift (σ a))
  rw [map_sub, map_mul, AlgEquiv.symm_apply_apply, hinv, hC, AlgEquiv.commutes, ← hC] at hs
  exact ⟨_, hs⟩

end GlobalTheory.CycFr
