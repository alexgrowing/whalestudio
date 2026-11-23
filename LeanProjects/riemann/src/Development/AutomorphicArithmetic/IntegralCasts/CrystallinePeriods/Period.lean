import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

theorem eq_C_of_derivative_eq_zero (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) {f : Polynomial A}
    (hf : Polynomial.derivative f = 0) : f = Polynomial.C (f.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · have h1 := Polynomial.coeff_derivative f n
    rw [hf, Polynomial.coeff_zero] at h1
    rw [Polynomial.coeff_C_succ]
    exact (h n).mul_left_eq_zero.1 h1.symm

theorem derivative_surjective (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) :
    Function.Surjective (Polynomial.derivative : Polynomial A → Polynomial A) := by
  intro f
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨f', rfl⟩ := hf
    obtain ⟨g', rfl⟩ := hg
    exact ⟨f' + g', map_add _ _ _⟩
  | monomial n a =>
    obtain ⟨b, hb⟩ := (h n).exists_left_inv
    refine ⟨Polynomial.monomial (n + 1) (a * b), ?_⟩
    rw [Polynomial.derivative_monomial_succ, mul_assoc, hb, mul_one]

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add, map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring

theorem Acris.logTeich_padicPow_eq_smul (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = a • Acris.logTeich η := by
  rw [Acris.logTeich_padicPow, Algebra.smul_def]

variable (p R) in

def Acris.logTeichLinear : Additive (tateModule p R) →ₗ[ℤ_[p]] Acris p R where
  toFun η := Acris.logTeich η.toMul
  map_add' _ _ := Acris.logTeich_mul _ _
  map_smul' a η := Acris.logTeich_padicPow_eq_smul η.toMul a

theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

theorem Bcris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Bcris.logTeich (padicPow η a) = algebraMap ℚ_[p] (Bcris p R) a * Bcris.logTeich η := by
  rw [Bcris.logTeich, Acris.logTeich_padicPow, map_mul, Bcris.algebraMap_padicInt]
  rfl

theorem Bcris.isUnit_natCast_add_one (n : ℕ) : IsUnit ((n : Bcris p R) + 1) := by
  have : IsUnit ((n : ℚ_[p]) + 1) := IsUnit.mk0 _ (Nat.cast_add_one_ne_zero n)
  simpa using this.map (algebraMap ℚ_[p] (Bcris p R))

theorem IsPrimitive.isLocalization_away [IsDomain R] {ε : tateModule p R} (hε : IsPrimitive ε) :
    IsLocalization.Away (algebraMap (Acris p R) (BcrisPlus p R) (Acris.logTeich ε))
      (Bcris p R) := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := Bcris p R) _ (BcrisPlus.periods p R)
    ?_ ?_).2 inferInstance
  · exact Submonoid.powers_le.2 (Submonoid.subset_closure ⟨ε, hε, rfl⟩)
  · intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨ε', hε', rfl⟩ := hx
      obtain ⟨a, ha⟩ := hε'.exists_unit hε
      refine ⟨_, Submonoid.mem_powers _, ?_⟩
      rw [ha, Acris.logTeich_padicPow, map_mul]
      exact dvd_mul_left _ _
    | one => exact ⟨1, one_mem _, dvd_rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      exact ⟨a * b, mul_mem ha hb, mul_dvd_mul hxa hyb⟩

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]

variable (p R)

def Acris.t : Acris p R := Acris.logTeich (eps p R)

def BcrisPlus.t : BcrisPlus p R := algebraMap (Acris p R) _ (Acris.t p R)

def Bcris.t : Bcris p R := algebraMap (Acris p R) _ (Acris.t p R)

theorem Bcris.t_eq_logTeich : Bcris.t p R = Bcris.logTeich (eps p R) := rfl

theorem Bcris.algebraMap_alt : algebraMap (BcrisPlus p R) (Bcris p R) (BcrisPlus.t p R) =
    Bcris.t p R := rfl

instance Bcris.isLocalization_away_alt : IsLocalization.Away (BcrisPlus.t p R) (Bcris p R) :=
  (isPrimitive_eps p R).isLocalization_away

theorem Bcris.isUnit_cyclotomicPeriod_deRham : IsUnit (Bcris.t p R) := Bcris.isUnit_logTeich (isPrimitive_eps p R)

variable {p R} in

theorem Acris.exists_logTeich_eq_smul_t (η : tateModule p R) :
    ∃ a : ℤ_[p], Acris.logTeich η = a • Acris.t p R := by
  obtain ⟨a, rfl⟩ := (isPrimitive_eps p R).padicPow_surjective η
  exact ⟨a, Acris.logTeich_padicPow_eq_smul _ a⟩

theorem Acris.crisFrobenius_periodT_eq_prime_smul : Acris.frob p R (Acris.t p R) = p * Acris.t p R := Acris.frob_logTeich _

theorem Bcris.crisFrobenius_periodT_eq_prime_smul : Bcris.frob p R (Bcris.t p R) = p * Bcris.t p R := Bcris.frob_logTeich _

variable {p R}

theorem tateModule.map_eq_padicPow (e : R ≃+* R) (η : tateModule p R) :
    tateModule.map p (e : R →+* R) η = padicPow η (cyclotomicCharacter R p e) :=
  Subtype.ext (tateModule.map_eq_padicPow_cyclotomicCharacter e η)

theorem Acris.map_logTeich_eq_smul (e : R ≃+* R) (η : tateModule p R) :
    Acris.map p (e : R →+* R) (Acris.logTeich η) =
      (cyclotomicCharacter R p e : ℤ_[p]) • Acris.logTeich η := by
  rw [Acris.map_logTeich, tateModule.map_eq_padicPow, Acris.logTeich_padicPow_eq_smul]

theorem Acris.map_t (e : R ≃+* R) :
    Acris.map p (e : R →+* R) (Acris.t p R) = (cyclotomicCharacter R p e : ℤ_[p]) • Acris.t p R :=
  Acris.map_logTeich_eq_smul e _

theorem Bcris.map_t (e : R ≃+* R) (he : Function.Injective (e : R →+* R)) :
    Bcris.map p (e : R →+* R) he (Bcris.t p R) =
      ((cyclotomicCharacter R p e : ℤ_[p]) : ℚ_[p]) • Bcris.t p R := by
  rw [Bcris.t_eq_logTeich, Bcris.map_logTeich, tateModule.map_eq_padicPow,
    Bcris.logTeich_padicPow, Algebra.smul_def]

def PFlat.cocycle (ϖ : PFlat p R) (e : R ≃+* R) : ℤ_[p] :=
  ((isPrimitive_eps p R).padicPowEquiv.symm ((PFlat.map p (e : R →+* R) ϖ).div ϖ)).toAdd

theorem PFlat.padicPow_cocycle (ϖ : PFlat p R) (e : R ≃+* R) :
    padicPow (eps p R) (ϖ.cocycle e) = (PFlat.map p (e : R →+* R) ϖ).div ϖ :=
  (isPrimitive_eps p R).padicPowEquiv.apply_symm_apply _

theorem PFlat.map_eq_twist (ϖ : PFlat p R) (e : R ≃+* R) :
    PFlat.map p (e : R →+* R) ϖ = ϖ.twist (padicPow (eps p R) (ϖ.cocycle e)) := by
  rw [PFlat.padicPow_cocycle, PFlat.twist_div]

theorem PFlat.cocycle_eq_iff (ϖ : PFlat p R) (e : R ≃+* R) (c : ℤ_[p]) :
    ϖ.cocycle e = c ↔ PFlat.map p (e : R →+* R) ϖ = ϖ.twist (padicPow (eps p R) c) := by
  rw [PFlat.map_eq_twist]
  exact ((PFlat.twist_injective ϖ).comp (isPrimitive_eps p R).padicPow_injective).eq_iff.symm

theorem PFlat.cocycle_mul (ϖ : PFlat p R) (e e' : R ≃+* R) :
    ϖ.cocycle (e * e') = ϖ.cocycle e + cyclotomicCharacter R p e * ϖ.cocycle e' := by
  have h : ((e * e' : R ≃+* R) : R →+* R) = (e : R →+* R).comp (e' : R →+* R) := rfl
  rw [PFlat.cocycle_eq_iff, h, ← PFlat.map_map, ϖ.map_eq_twist e', PFlat.map_twist,
    ϖ.map_eq_twist e, PFlat.twist_twist, tateModule.map_eq_padicPow, ← padicPow_mul,
    ← padicPow_add, add_comm, mul_comm]

theorem Bst.map_logFlat_eq_add (e : R ≃+* R) (he : Function.Injective (e : R →+* R))
    (ϖ : PFlat p R) :
    Bst.map p (e : R →+* R) he (Bst.logFlat ϖ) =
      Bst.logFlat ϖ + algebraMap (Bcris p R) _ ((ϖ.cocycle e : ℚ_[p]) • Bcris.t p R) := by
  rw [Bst.map_logFlat, PFlat.map_eq_twist, Bst.logFlat_twist, Bcris.logTeich_padicPow, add_comm,
    Algebra.smul_def, Bcris.t_eq_logTeich]

end Good

namespace Bst

open Polynomial

theorem monodromy_aeval (ϖ : PFlat p R) (f : (Bcris p R)[X]) :
    monodromy p R (aeval (logFlat ϖ) f) = -aeval (logFlat ϖ) (derivative f) := by
  rw [Derivation.map_aeval, monodromy_logFlat, smul_neg, smul_eq_mul, mul_one]

variable [IsDomain R] [CharZero R] [ValuationRing R]

def toPolynomial (ϖ : PFlat p R) : Bst p R →ₐ[Bcris p R] (Bcris p R)[X] :=
  { lift (C : Bcris p R →+* (Bcris p R)[X]) (fun ϖ' => C (Bcris.logTeich (ϖ'.div ϖ)) + X)
      (fun η ϖ' => by rw [PFlat.twist_div_eq, Bcris.logTeich_mul, map_add, add_assoc]) with
    commutes' := fun x => lift_algebraMap _ _ _ x }

theorem toPolynomial_logFlat (ϖ ϖ' : PFlat p R) :
    toPolynomial ϖ (logFlat ϖ') = C (Bcris.logTeich (ϖ'.div ϖ)) + X :=
  lift_logFlat (C : Bcris p R →+* (Bcris p R)[X]) (fun ϖ' => C (Bcris.logTeich (ϖ'.div ϖ)) + X)
    (fun η ϖ' => by rw [PFlat.twist_div_eq, Bcris.logTeich_mul, map_add, add_assoc]) ϖ'

def polynomialEquiv (ϖ : PFlat p R) : (Bcris p R)[X] ≃ₐ[Bcris p R] Bst p R :=
  AlgEquiv.ofAlgHom (aeval (logFlat ϖ)) (toPolynomial ϖ)
    (AlgHom.coe_ringHom_injective (hom_ext (fun x => by simp) (fun ϖ' => by
      change aeval (logFlat ϖ) (toPolynomial ϖ (logFlat ϖ')) = logFlat ϖ'
      rw [toPolynomial_logFlat, map_add, aeval_C, aeval_X, ← logFlat_twist, PFlat.twist_div])))
    (Polynomial.algHom_ext (by simp [toPolynomial_logFlat]))

theorem polynomialEquiv_apply (ϖ : PFlat p R) (f : (Bcris p R)[X]) :
    polynomialEquiv ϖ f = aeval (logFlat ϖ) f := rfl

@[simp] theorem polynomialEquiv_X (ϖ : PFlat p R) : polynomialEquiv ϖ X = logFlat ϖ :=
  aeval_X _

@[simp] theorem polynomialEquiv_C (ϖ : PFlat p R) (x : Bcris p R) :
    polynomialEquiv ϖ (C x) = algebraMap _ _ x := aeval_C _ _

theorem monodromy_polynomialEquiv (ϖ : PFlat p R) (f : (Bcris p R)[X]) :
    monodromy p R (polynomialEquiv ϖ f) = -polynomialEquiv ϖ (derivative f) :=
  monodromy_aeval ϖ f

theorem monodromy_iterate_polynomialEquiv (ϖ : PFlat p R) (f : (Bcris p R)[X]) (n : ℕ) :
    (monodromy p R)^[n] (polynomialEquiv ϖ f) =
      (-1) ^ n * polynomialEquiv ϖ (derivative^[n] f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ((-1) ^ n : Bst p R) = algebraMap (Bcris p R) _ ((-1) ^ n) := by simp
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', pow_succ, h,
      ← Algebra.smul_def, Derivation.map_smul, monodromy_polynomialEquiv, Algebra.smul_def]
    ring

theorem transcendental_logFlat (ϖ : PFlat p R) : Transcendental (Bcris p R) (logFlat ϖ) :=
  transcendental_iff_injective.2 (polynomialEquiv ϖ).injective

variable [IsAlgClosed (FractionRing R)]

variable (p R) in
theorem algebraMap_injective : Function.Injective (algebraMap (Bcris p R) (Bst p R)) := by
  intro x y h
  rw [← polynomialEquiv_C (pflat p R), ← polynomialEquiv_C (pflat p R)] at h
  exact C_injective ((polynomialEquiv _).injective h)

variable (p R) in

theorem monodromy_surjective : Function.Surjective (monodromy p R) := by
  intro x
  obtain ⟨f, rfl⟩ := (polynomialEquiv (pflat p R)).surjective x
  obtain ⟨g, rfl⟩ := derivative_surjective Bcris.isUnit_natCast_add_one f
  exact ⟨polynomialEquiv _ (-g), by rw [monodromy_polynomialEquiv, map_neg, map_neg, neg_neg]⟩

theorem monodromy_eq_zero_iff (x : Bst p R) :
    monodromy p R x = 0 ↔ x ∈ Set.range (algebraMap (Bcris p R) (Bst p R)) := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := (polynomialEquiv (pflat p R)).surjective x
    rw [monodromy_polynomialEquiv, neg_eq_zero, map_eq_zero_iff _ (polynomialEquiv _).injective]
      at h
    rw [eq_C_of_derivative_eq_zero Bcris.isUnit_natCast_add_one h, polynomialEquiv_C]
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Derivation.map_algebraMap _ y

theorem exists_monodromy_iterate_eq_zero (x : Bst p R) : ∃ n, (monodromy p R)^[n] x = 0 := by
  obtain ⟨f, rfl⟩ := (polynomialEquiv (pflat p R)).surjective x
  exact ⟨f.natDegree + 1, by
    rw [monodromy_iterate_polynomialEquiv, iterate_derivative_eq_zero (Nat.lt_succ_self _),
      map_zero, mul_zero]⟩

variable (p R) in

def u : Bst p R := logFlat (pflat p R)

theorem frob_u : frob p R (u p R) = p * u p R := frob_logFlat _

@[simp] theorem monodromy_u : monodromy p R (u p R) = -1 := monodromy_logFlat _

end Bst

end Reformulated.AutPerF
