import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

noncomputable section

open PowerSeries Formalism Formalism.BasicNotions

namespace GlobalTheory.Fon

section Series

theorem ps_hom_ext {R B : Type} [CommRing R] [CommRing B] {f g : R⟦X⟧ →+* B}
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hsep : ∀ b : B, (∀ n, f X ^ n ∣ b) → b = 0) :
    f = g := by
  have hp : ∀ p : Polynomial R, f p = g p := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => simp [hp, hq]
    | monomial n a _ => simp [hC, hX]
  ext1 a
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  rw [a.eq_X_pow_mul_shift_add_trunc n, map_add, map_add, hp, map_mul, map_mul, map_pow, map_pow, ← hX]
  exact ⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩

theorem eq_zero_of_pow_dvd {R : Type} [CommRing R] {a : R⟦X⟧} (ha : constantCoeff a = 0) (b : R⟦X⟧)
    (h : ∀ n, a ^ n ∣ b) : b = 0 := by
  ext n
  have : (X : R⟦X⟧) ^ (n + 1) ∣ b := (pow_dvd_pow_of_dvd (X_dvd_iff.2 ha) _).trans (h _)
  simpa using X_pow_dvd_iff.1 this n n.lt_succ_self

variable (l : ℕ) (R : Type) [CommRing R]

def phi0 : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' (a := (1 + X : R⟦X⟧) ^ l - 1) (by simp))

@[simp] theorem cyclotomicFrobeniusPowerSeries_X : phi0 l R X = (1 + X) ^ l - 1 := substAlgHom_X _

@[simp] theorem cyclotomicFrobeniusPowerSeries_C (r : R) : phi0 l R (C r) = C r := (phi0 l R).commutes r

def qq : R⟦X⟧ := ∑ k ∈ Finset.range l, (1 + X) ^ k

def Xs (s : ℕ) : R⟦X⟧ := (1 + X) ^ (l ^ (s - 1)) - 1

def Qs (s : ℕ) : R⟦X⟧ := ∑ k ∈ Finset.range l, (1 + Xs l R s) ^ k

def es (s : ℕ) : ℕ := l ^ (s - 1) * (l - 1)

theorem X_mul_qq : X * qq l R = (1 + X) ^ l - 1 := by
  rw [← mul_geom_sum, add_sub_cancel_left, qq]

theorem cyclotomicFrobeniusPowerSeries_X_eq_mul_quotient : phi0 l R X = X * qq l R := by rw [X_mul_qq, cyclotomicFrobeniusPowerSeries_X]

theorem cyclotomicFrobeniusPowerSeries_pow_apply_X (m : ℕ) : (phi0 l R ^ m) X = (1 + X) ^ (l ^ m) - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ih]; simp [← pow_mul, pow_succ']

theorem Xs_eq (s : ℕ) : Xs l R s = (phi0 l R ^ (s - 1)) X := (cyclotomicFrobeniusPowerSeries_pow_apply_X l R _).symm

theorem cyclotomicFrobenius_iteratedVariable_eq_mul (s : ℕ) : phi0 l R (Xs l R s) = Xs l R s * Qs l R s := by
  have h := mul_geom_sum (1 + Xs l R s) l
  rw [add_sub_cancel_left] at h
  rw [Qs, h]
  simp [Xs, ← pow_mul, mul_comm]

variable {R} in

def phiS (Fr : R →+* R) : R⟦X⟧ →+* R⟦X⟧ := (phi0 l R : R⟦X⟧ →+* R⟦X⟧).comp (PowerSeries.map Fr)

@[simp] theorem phiS_X (Fr : R →+* R) : phiS l Fr X = (1 + X) ^ l - 1 := by simp [phiS]

@[simp] theorem phiS_C (Fr : R →+* R) (r : R) : phiS l Fr (C r) = C (Fr r) := by simp [phiS]

variable {l} [Fact l.Prime] [Algebra ℤ_[l] R]

def gam (c : ℤ_[l]) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' (a := binomialSeries R c - 1) (by simp))

@[simp] theorem gam_X (c : ℤ_[l]) : gam R c X = binomialSeries R c - 1 := substAlgHom_X _

@[simp] theorem gam_C (c : ℤ_[l]) (r : R) : gam R c (C r) = C r := (gam R c).commutes r

theorem constantCoeff_gam_X (c : ℤ_[l]) : constantCoeff (gam R c X) = 0 := by simp

theorem coeff_one_gam_X (c : ℤ_[l]) : coeff 1 (gam R c X) = algebraMap ℤ_[l] R c := by
  simp [Algebra.algebraMap_eq_smul_one, coeff_one]

variable {R} in

theorem map_binomialSeries {R' : Type} [CommRing R'] [Algebra ℤ_[l] R'] (h : R →+* R')
    (hh : ∀ z : ℤ_[l], h (algebraMap _ _ z) = algebraMap _ _ z) (c : ℤ_[l]) :
    PowerSeries.map h (binomialSeries R c) = binomialSeries R' c := by
  ext n
  simp [← Algebra.algebraMap_eq_smul_one, hh]

variable {R} in

theorem map_gam {R' : Type} [CommRing R'] [Algebra ℤ_[l] R'] (h : R →+* R')
    (hh : ∀ z : ℤ_[l], h (algebraMap _ _ z) = algebraMap _ _ z) (c : ℤ_[l]) (a : R⟦X⟧) :
    PowerSeries.map h (gam R c a) = gam R' c (PowerSeries.map h a) := by
  refine RingHom.congr_fun (ps_hom_ext (f := (PowerSeries.map h).comp (gam R c : R⟦X⟧ →+* R⟦X⟧))
    (g := (gam R' c : R'⟦X⟧ →+* R'⟦X⟧).comp (PowerSeries.map h)) (by simp) ?_ ?_) a
  · simp [map_binomialSeries h hh]
  · exact eq_zero_of_pow_dvd (by simp [map_binomialSeries h hh])

private theorem coeff_ode (f : ℤ_[l]⟦X⟧) (n : ℕ) :
    coeff n ((1 + X) * d⁄dX ℤ_[l] f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
  rw [add_mul, one_mul, map_add, coeff_derivative]
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp

private theorem ode_binomial (c : ℤ_[l]) :
    (1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c) = C c * binomialSeries ℤ_[l] c := by
  ext n
  rw [coeff_ode, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h0 : (n.factorial : ℤ_[l]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h1

private theorem ode_unique (c : ℤ_[l]) {f g : ℤ_[l]⟦X⟧} (hf : (1 + X) * d⁄dX ℤ_[l] f = C c * f)
    (hg : (1 + X) * d⁄dX ℤ_[l] g = C c * g) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_ode, coeff_C_mul] at h1 h2
    have h3 : ((n : ℤ_[l]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [ih] at h1
    linear_combination h1 - h2

theorem gam_binomialSeries (c c' : ℤ_[l]) :
    gam R c (binomialSeries R c') = binomialSeries R (c * c') := by
  have key : gam ℤ_[l] c (binomialSeries ℤ_[l] c') = binomialSeries ℤ_[l] (c * c') := by
    have hs : HasSubst (binomialSeries ℤ_[l] c - 1) := HasSubst.of_constantCoeff_zero' (by simp)
    have e : ∀ f, gam ℤ_[l] c f = subst (binomialSeries ℤ_[l] c - 1) f := fun f =>
      congrFun (coe_substAlgHom hs) f
    refine ode_unique (c * c') ?_ (ode_binomial _) ?_
    · have h1 := congrArg (gam ℤ_[l] c) (ode_binomial c')
      rw [map_mul, map_mul, map_add, map_one, gam_X, gam_C] at h1
      have h2 := ode_binomial c
      have h3 : d⁄dX ℤ_[l] (gam ℤ_[l] c (binomialSeries ℤ_[l] c')) =
          gam ℤ_[l] c (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c')) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c) := by
        rw [e, e, derivative_subst hs]; simp
      rw [h3, map_mul]
      linear_combination (gam ℤ_[l] c (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c'))) * h2 + C c * h1
    · obtain ⟨b, hb⟩ : (X : ℤ_[l]⟦X⟧) ∣ binomialSeries ℤ_[l] c' - 1 := X_dvd_iff.2 (by simp)
      rw [sub_eq_iff_eq_add.1 hb]
      simp
  have h := congrArg (PowerSeries.map (algebraMap ℤ_[l] R)) key
  rwa [map_gam _ (fun _ => rfl), map_binomialSeries _ (fun _ => rfl),
    map_binomialSeries _ (fun _ => rfl)] at h

variable {R} in

theorem algHom_ext_X {f g : R⟦X⟧ →ₐ[R] R⟦X⟧} (h : f X = g X) (h0 : constantCoeff (f X) = 0) : f = g :=
  AlgHom.coe_ringHom_injective (ps_hom_ext
    (fun r => (f.commutes r).trans (g.commutes r).symm) h (eq_zero_of_pow_dvd h0))

def gamHom : ℤ_[l] →* (R⟦X⟧ →ₐ[R] R⟦X⟧) where
  toFun := gam R
  map_one' := algHom_ext_X (by
    have := binomialSeries_nat (R := ℤ_[l]) (A := R) 1
    simp_all) (by simp)
  map_mul' c c' := algHom_ext_X (by simp [gam_binomialSeries]) (by simp)

theorem gam_mul (c c' : ℤ_[l]) (a : R⟦X⟧) : gam R (c * c') a = gam R c (gam R c' a) :=
  congrArg (fun f => f a) ((gamHom R).map_mul c c')

@[simp] theorem gam_one (a : R⟦X⟧) : gam R (1 : ℤ_[l]) a = a :=
  congrArg (fun f => f a) (gamHom (l := l) R).map_one

theorem gam_l : gam R (l : ℤ_[l]) = phi0 l R := algHom_ext_X (by simp) (by simp)

theorem cyclotomicFrobenius_comm_gammaAction (c : ℤ_[l]) (a : R⟦X⟧) : phi0 l R (gam R c a) = gam R c (phi0 l R a) := by
  rw [← gam_l, ← gam_mul, ← gam_mul, mul_comm]

def gamAut : ℤ_[l]ˣ →* (R⟦X⟧ ≃ₐ[R] R⟦X⟧) :=
  (AlgEquiv.algHomUnitsEquiv R R⟦X⟧).toMonoidHom.comp (Units.map (gamHom R))

@[simp] theorem gamAut_apply (c : ℤ_[l]ˣ) (a : R⟦X⟧) : gamAut R c a = gam R (c : ℤ_[l]) a := rfl

def vser (c : ℤ_[l]) : R⟦X⟧ := PowerSeries.mk fun k => Ring.choose c (k + 1) • (1 : R)

theorem gam_X_eq (c : ℤ_[l]) : gam R c X = X * vser R c := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [vser, coeff_succ_X_mul, coeff_one]

theorem constantCoeff_vser (c : ℤ_[l]) : constantCoeff (vser R c) = algebraMap ℤ_[l] R c := by
  simp [vser, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_eq_smul_one]

theorem isUnit_vser (c : ℤ_[l]ˣ) : IsUnit (vser R (c : ℤ_[l])) :=
  isUnit_iff_constantCoeff.2 (by rw [constantCoeff_vser]; exact c.isUnit.map _)

end Series

section Complete

variable (l : ℕ)

abbrev LComplete (B : Type) [CommRing B] : Prop := IsAdicComplete (Ideal.span {(l : B)}) B

variable {l}

theorem eq_zero_of_l_pow_dvd {B : Type} [CommRing B] [IsHausdorff (Ideal.span {(l : B)}) B] (b : B)
    (h : ∀ k, (l : B) ^ k ∣ b) : b = 0 :=
  IsHausdorff.haus (I := Ideal.span {(l : B)}) inferInstance b fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h k

theorem isUnit_of_l_dvd {B : Type} [CommRing B] [LComplete l B] {u x : B} (hu : IsUnit u)
    (h : (l : B) ∣ x - u) : IsUnit x := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 := Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B)}) (Ideal.mem_span_singleton.2 h)) v
  have h2 : (x - u) * v + 1 = x * v := by linear_combination -hv
  rw [h2] at h1
  exact isUnit_of_mul_isUnit_left h1

variable (l) (R : Type) [CommRing R]

def completedLocalizedPowerSeriesRing : Type := AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))

instance : CommRing (completedLocalizedPowerSeriesRing l R) := inferInstanceAs (CommRing (AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))))

instance algEE1 {Z : Type} [CommRing Z] [Algebra Z R⟦X⟧] : Algebra Z (completedLocalizedPowerSeriesRing l R) :=
  inferInstanceAs (Algebra Z (AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))))

def ofLoc : Localization.Away (X : R⟦X⟧) →+* completedLocalizedPowerSeriesRing l R :=
  algebraMap _ (AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧)))

abbrev ιE : R⟦X⟧ →+* completedLocalizedPowerSeriesRing l R := algebraMap _ _

theorem ofLoc_alg (a : R⟦X⟧) : ofLoc l R (algebraMap _ _ a) = ιE l R a := rfl

instance towEE1 {Z : Type} [CommRing Z] [Algebra Z R⟦X⟧] : IsScalarTower Z R⟦X⟧ (completedLocalizedPowerSeriesRing l R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance towEE1' {Z : Type} [CommRing Z] [Algebra Z R] : IsScalarTower Z R (completedLocalizedPowerSeriesRing l R) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply Z R⟦X⟧ (completedLocalizedPowerSeriesRing l R), IsScalarTower.algebraMap_apply R R⟦X⟧ (completedLocalizedPowerSeriesRing l R),
      IsScalarTower.algebraMap_apply Z R R⟦X⟧]

theorem algebraMap_completedLocalization (r : R) : algebraMap R (completedLocalizedPowerSeriesRing l R) r = ιE l R (C r) := rfl

theorem isUnit_ιE_X : IsUnit (ιE l R X) :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (X : R⟦X⟧)) X).map (ofLoc l R)

private theorem mem_iff' (S : Type) [CommRing S] (k : ℕ) (x : AdicCompletion (Ideal.span {(l : S)}) S) : (l : AdicCompletion (Ideal.span {(l : S)}) S) ^ k ∣ x ↔
    AdicCompletion.eval (Ideal.span {(l : S)}) S k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, by rw [Algebra.smul_def, map_pow, map_natCast]⟩
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, map_pow, map_natCast]⟩

private theorem mem_iff (k : ℕ) (x : completedLocalizedPowerSeriesRing l R) : (l : completedLocalizedPowerSeriesRing l R) ^ k ∣ x ↔
    AdicCompletion.eval (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) _ k x = 0 :=
  mem_iff' l _ k x

instance instLAdicCompleteCompletedLocalizedPowerSeries : LComplete l (completedLocalizedPowerSeriesRing l R) := by
  have h := (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧)))
    (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧)))).2
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

variable {l R}

theorem exists_loc (x : completedLocalizedPowerSeriesRing l R) (k : ℕ) : ∃ y, (l : completedLocalizedPowerSeriesRing l R) ^ k ∣ x - ofLoc l R y := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) _ k x)
  refine ⟨y, (mem_iff l R k _).2 ?_⟩
  erw [map_sub, ← hy]
  exact sub_self _

theorem completedLocalizedPowerSeries_dense_clearDenominators (x : completedLocalizedPowerSeriesRing l R) (k : ℕ) :
    ∃ (a : R⟦X⟧) (m : ℕ), (l : completedLocalizedPowerSeriesRing l R) ^ k ∣ x * ιE l R (X ^ m) - ιE l R a := by
  obtain ⟨y, hy⟩ := exists_loc x k
  obtain ⟨⟨a, _, m, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (X : R⟦X⟧)) y
  refine ⟨a, m, ?_⟩
  rw [← ofLoc_alg, ← ofLoc_alg, ← h, map_mul, ← sub_mul]
  exact hy.mul_right _

theorem prime_pow_dvd_of_dvd_completedLocalization (a : R⟦X⟧) (k : ℕ) (h : (l : completedLocalizedPowerSeriesRing l R) ^ k ∣ ιE l R a) : (l : R⟦X⟧) ^ k ∣ a := by
  have h1 : algebraMap _ (Localization.Away (X : R⟦X⟧)) a ∈
      (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) ^ k • (⊤ : Submodule _ _) :=
    (Submodule.Quotient.mk_eq_zero _).1 ((mem_iff l R k _).1 h)
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨⟨b, _, m, rfl⟩, h2⟩ := IsLocalization.surj (Submonoid.powers (X : R⟦X⟧)) y
  have h3 : a * X ^ m = (l : R⟦X⟧) ^ k * b := by
    apply IsLocalization.injective (M := Submonoid.powers (X : R⟦X⟧)) (Localization.Away (X : R⟦X⟧))
      (Submonoid.powers_le.2 (MvPowerSeries.X_mem_nonzeroDivisors (i := ())))
    rw [map_mul, map_mul, hy, mul_assoc, map_pow _ (l : R⟦X⟧), map_natCast]
    exact congrArg _ h2
  have hc : (l : R⟦X⟧) ^ k = C ((l : R) ^ k) := by simp
  refine ⟨PowerSeries.mk fun n => coeff (n + m) b, ?_⟩
  ext n
  rw [hc, coeff_C_mul, coeff_mk, ← coeff_C_mul, ← hc, ← h3, coeff_mul_X_pow]

theorem ιE_injective [IsHausdorff (Ideal.span {(l : R)}) R] : Function.Injective (ιE l R) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  ext n
  refine eq_zero_of_l_pow_dvd (l := l) _ fun k => ?_
  obtain ⟨b, rfl⟩ := prime_pow_dvd_of_dvd_completedLocalization (l := l) a k (by rw [ha]; exact dvd_zero _)
  have hc : (l : R⟦X⟧) ^ k = C ((l : R) ^ k) := by simp
  exact ⟨_, by rw [hc, coeff_C_mul]⟩

theorem completedLocalizedPowerSeries_ringHom_ext {B : Type} [CommRing B] [IsHausdorff (Ideal.span {(l : B)}) B]
    {f g : completedLocalizedPowerSeriesRing l R →+* B} (h : ∀ a, f (ιE l R a) = g (ιE l R a)) : f = g := by
  have h1 : f.comp (ofLoc l R) = g.comp (ofLoc l R) :=
    IsLocalization.ringHom_ext (Submonoid.powers (X : R⟦X⟧)) (RingHom.ext h)
  ext x
  rw [← sub_eq_zero]
  refine eq_zero_of_l_pow_dvd (l := l) _ fun k => ?_
  obtain ⟨y, z, hz⟩ := exists_loc x k
  have h2 : f (ofLoc l R y) = g (ofLoc l R y) := RingHom.congr_fun h1 y
  rw [sub_eq_iff_eq_add.1 hz]
  exact ⟨f z - g z, by simp [h2, mul_sub]⟩

def liftE {B : Type} [CommRing B] [LComplete l B] (f : R⟦X⟧ →+* B) (hf : IsUnit (f X)) :
    completedLocalizedPowerSeriesRing l R →+* B :=
  ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm : _ →+* B).comp
    (GlobalTheory.AdicMaps.padicMap l (IsLocalization.Away.lift (S := Localization.Away (X : R⟦X⟧)) X hf))

@[simp] theorem liftE_ιE {B : Type} [CommRing B] [LComplete l B] (f : R⟦X⟧ →+* B) (hf : IsUnit (f X))
    (a : R⟦X⟧) : liftE (l := l) f hf (ιE l R a) = f a := by
  have h := GlobalTheory.AdicMaps.padicMap_alg l (IsLocalization.Away.lift (S := Localization.Away (X : R⟦X⟧)) X hf)
    (algebraMap _ _ a)
  rw [IsLocalization.Away.lift_eq] at h
  exact (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm h).trans
    ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm.commutes _)

def mapE {R' : Type} [CommRing R'] (h : R →+* R') : completedLocalizedPowerSeriesRing l R →+* completedLocalizedPowerSeriesRing l R' :=
  liftE ((ιE l R').comp (PowerSeries.map h)) (by simpa using isUnit_ιE_X l R')

@[simp] theorem mapE_ιE {R' : Type} [CommRing R'] (h : R →+* R') (a : R⟦X⟧) :
    mapE h (ιE l R a) = ιE l R' (PowerSeries.map h a) := liftE_ιE _ _ _

variable [Fact l.Prime]

variable (l R) in

theorem isUnit_ιE_phi : IsUnit (ιE l R ((1 + X) ^ l - 1)) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : R⟦X⟧) X
  refine isUnit_of_l_dvd (l := l) ((isUnit_ιE_X l R).pow l) ⟨ιE l R (X * r), ?_⟩
  rw [hr]; simp; ring

def phiES (Fr : R →+* R) : completedLocalizedPowerSeriesRing l R →+* completedLocalizedPowerSeriesRing l R :=
  liftE ((ιE l R).comp (phiS l Fr)) (by rw [RingHom.comp_apply, phiS_X]; exact isUnit_ιE_phi l R)

@[simp] theorem phiES_ιE (Fr : R →+* R) (a : R⟦X⟧) : phiES Fr (ιE l R a) = ιE l R (phiS l Fr a) :=
  liftE_ιE _ _ _

variable (l R) in

def completedLocalizedLinearFrobenius : completedLocalizedPowerSeriesRing l R →ₐ[R] completedLocalizedPowerSeriesRing l R where
  toRingHom := phiES (RingHom.id R)
  commutes' r := by simp [algebraMap_completedLocalization]

@[simp] theorem completedLocalizedLinearFrobenius_comp (a : R⟦X⟧) : completedLocalizedLinearFrobenius l R (ιE l R a) = ιE l R (phi0 l R a) :=
  (phiES_ιE (RingHom.id R) a).trans (by simp [phiS])

variable (l R) in

theorem isUnit_ιE_phi_pow (m : ℕ) : IsUnit (ιE l R ((phi0 l R ^ m) X)) := by
  induction m with
  | zero => exact isUnit_ιE_X l R
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ← completedLocalizedLinearFrobenius_comp]; exact ih.map _

variable (l R) in

theorem isUnit_ιE_Xs (s : ℕ) : IsUnit (ιE l R (Xs l R s)) := Xs_eq l R s ▸ isUnit_ιE_phi_pow l R _

variable (l R) in

theorem isUnit_ιE_Qs (s : ℕ) : IsUnit (ιE l R (Qs l R s)) := by
  have h := (isUnit_ιE_Xs l R s).map (completedLocalizedLinearFrobenius l R)
  rw [completedLocalizedLinearFrobenius_comp, cyclotomicFrobenius_iteratedVariable_eq_mul, map_mul] at h
  exact isUnit_of_mul_isUnit_right h

variable [Algebra ℤ_[l] R]

variable (R) in

def completedLocalizedGammaAction (c : ℤ_[l]ˣ) : completedLocalizedPowerSeriesRing l R →ₐ[R] completedLocalizedPowerSeriesRing l R where
  toRingHom := liftE ((ιE l R).comp (gam R (c : ℤ_[l]) : R⟦X⟧ →+* R⟦X⟧)) (by
    change IsUnit (ιE l R (gam R (c : ℤ_[l]) X))
    rw [gam_X_eq, map_mul]
    exact (isUnit_ιE_X l R).mul ((isUnit_vser R c).map _))
  commutes' r := by simp [algebraMap_completedLocalization]

@[simp] theorem completedLocalizedGammaAction_comp (c : ℤ_[l]ˣ) (a : R⟦X⟧) :
    completedLocalizedGammaAction R c (ιE l R a) = ιE l R (gam R (c : ℤ_[l]) a) := liftE_ιE _ _ _

variable (R) in

def completedLocalizedGammaActionHom : ℤ_[l]ˣ →* (completedLocalizedPowerSeriesRing l R →ₐ[R] completedLocalizedPowerSeriesRing l R) where
  toFun := completedLocalizedGammaAction R
  map_one' := AlgHom.coe_ringHom_injective (completedLocalizedPowerSeries_ringHom_ext fun a => by simp)
  map_mul' c c' := AlgHom.coe_ringHom_injective (completedLocalizedPowerSeries_ringHom_ext fun a => by simp [gam_mul])

end Complete

section Letters

variable (l : ℕ) (O : Type) [CommRing O] (n : ℕ)

def phiA : LetA O n →ₐ[O] LetA O n := letφ (phi0 l O)

abbrev EE : Type := ZMod n → completedLocalizedPowerSeriesRing l O

instance algEE : Algebra (LetA O n) (EE l O n) := Pi.instAlgebraForall _ _

instance towEE : IsScalarTower O (LetA O n) (EE l O n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem EE_isUnit_π : IsUnit (algebraMap (LetA O n) (EE l O n) letπ) :=
  Pi.isUnit_iff.2 fun _ => isUnit_ιE_X l O

theorem EE_inj [IsHausdorff (Ideal.span {(l : O)}) O] :
    Function.Injective (algebraMap (LetA O n) (EE l O n)) :=
  fun _ _ h => funext fun i => ιE_injective (l := l) (congrFun h i)

private theorem pi_dvd {ι : Type} {B : Type} [CommRing B] {x y : ι → B} : x ∣ y ↔ ∀ i, x i ∣ y i :=
  ⟨fun ⟨z, h⟩ i => ⟨z i, congrFun h i⟩, fun h => by
    choose z hz using h
    exact ⟨z, funext hz⟩⟩

instance lComplete_EE : LComplete l (EE l O n) where
  haus' x hx := funext fun i => eq_zero_of_l_pow_dvd (l := l) _ fun k => by
    have := hx k
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    exact pi_dvd.1 this i
  prec' x hx := by
    have h := fun i => IsPrecomplete.prec (I := Ideal.span {(l : completedLocalizedPowerSeriesRing l O)}) inferInstance
      (f := fun k => x k i) (fun {a b} hab => by
        have := hx hab
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] at this ⊢
        exact pi_dvd.1 this i)
    choose L hL using h
    refine ⟨L, fun k => ?_⟩
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hL ⊢
    exact pi_dvd.2 fun i => hL i k

theorem EE_dense [NeZero n] (x : EE l O n) (k : ℕ) : ∃ (a : LetA O n) (m : ℕ),
    x * algebraMap (LetA O n) (EE l O n) (letπ ^ m) - algebraMap (LetA O n) (EE l O n) a ∈
      Ideal.span {(l : EE l O n) ^ k} := by
  choose a m h using fun i => completedLocalizedPowerSeries_dense_clearDenominators (x i) k
  refine ⟨fun i => a i * X ^ (Finset.univ.sup m - m i), Finset.univ.sup m,
    Ideal.mem_span_singleton.2 (pi_dvd.2 fun i => ?_)⟩
  have h1 : m i + (Finset.univ.sup m - m i) = Finset.univ.sup m :=
    Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ i))
  have h2 := (h i).mul_right (ιE l O (X ^ (Finset.univ.sup m - m i)))
  rw [sub_mul, mul_assoc, ← map_mul, ← map_mul, ← pow_add, h1] at h2
  exact h2

theorem EE_sat (a : LetA O n) (k : ℕ)
    (h : algebraMap (LetA O n) (EE l O n) a ∈ Ideal.span {(l : EE l O n) ^ k}) :
    ∃ b : LetA O n, a = (l : LetA O n) ^ k * b :=
  pi_dvd.2 fun i => prime_pow_dvd_of_dvd_completedLocalization (a i) k (pi_dvd.1 (Ideal.mem_span_singleton.1 h) i)

variable [Fact l.Prime]

def phiEE : EE l O n →ₐ[O] EE l O n :=
  AlgHom.pi fun i => (completedLocalizedLinearFrobenius l O).comp (Pi.evalAlgHom O (fun _ : ZMod n => completedLocalizedPowerSeriesRing l O) (i - 1))

theorem phiEE_ext (a : LetA O n) : phiEE l O n (algebraMap (LetA O n) _ a) =
    algebraMap (LetA O n) _ (phiA l O n a) := funext fun _ => completedLocalizedLinearFrobenius_comp _

variable {l} [Algebra ℤ_[l] O]

def gamA (c : ℤ_[l]) : LetA O n →ₐ[O] LetA O n := letγ (gam O c)

def gamEE : ℤ_[l]ˣ →* (EE l O n →ₐ[O] EE l O n) where
  toFun c := AlgHom.pi fun i => (completedLocalizedGammaAction O c).comp (Pi.evalAlgHom O (fun _ : ZMod n => completedLocalizedPowerSeriesRing l O) i)
  map_one' := AlgHom.ext fun x => funext fun i =>
    congrArg (fun f => f (x i)) (completedLocalizedGammaActionHom (l := l) O).map_one
  map_mul' c c' := AlgHom.ext fun x => funext fun i =>
    congrArg (fun f => f (x i)) ((completedLocalizedGammaActionHom O).map_mul c c')

theorem gamEE_ext (c : ℤ_[l]ˣ) (a : LetA O n) : gamEE O n c (algebraMap (LetA O n) _ a) =
    algebraMap (LetA O n) _ (gamA O n (c : ℤ_[l]) a) := funext fun _ => completedLocalizedGammaAction_comp _ _

end Letters

example : phi0 2 ℤ X = X ^ 2 + 2 * X := by rw [cyclotomicFrobeniusPowerSeries_X]; ring

example : Qs 2 ℤ 2 = X ^ 2 + 2 * X + 2 := by simp [Qs, Xs, Finset.sum_range_succ]; ring

example (l : ℕ) [Fact l.Prime] : (1 + gam ℤ_[l] (-1 : ℤ_[l]) X) * (1 + X) = 1 := by
  have h := binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) 1
  rw [pow_one] at h
  rw [gam_X, add_sub_cancel, ← h, ← binomialSeries_add]
  simp

example (l : ℕ) [Fact l.Prime] : (l : completedLocalizedPowerSeriesRing l ℤ_[l]) ≠ 0 := by
  have : IsHausdorff (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  rw [← map_natCast (ιE l ℤ_[l]), map_ne_zero_iff _ ιE_injective]
  rw [← map_natCast (C : ℤ_[l] →+* _), map_ne_zero_iff _ C_injective]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

end GlobalTheory.Fon
