import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TameDifferent

private theorem trace_add_of_short_exact {k A M C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] [AddCommGroup C] [Module k C]
    [Module.Finite k M] (f : A →ₗ[k] M) (g : M →ₗ[k] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : ∀ a, g (f a) = 0) (hex : ∀ m, g m = 0 → ∃ a, f a = m)
    (α : A →ₗ[k] A) (φ : M →ₗ[k] M) (γ : C →ₗ[k] C)
    (h1 : ∀ a, φ (f a) = f (α a)) (h2 : ∀ m, g (φ m) = γ (g m)) :
    LinearMap.trace k M φ = LinearMap.trace k A α + LinearMap.trace k C γ := by
  have : Module.Finite k A := Module.Finite.of_injective f hf
  have : Module.Finite k C := Module.Finite.of_surjective g hg
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  obtain ⟨l, hl⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hs' : ∀ c, g (s c) = c := fun c => LinearMap.congr_fun hs c
  have hl' : ∀ a, l (f a) = a := fun a => LinearMap.congr_fun hl a
  let r : M →ₗ[k] A := l ∘ₗ (LinearMap.id - s ∘ₗ g)
  have hr : ∀ m, f (r m) = m - s (g m) := by
    intro m
    obtain ⟨a, ha⟩ := hex (m - s (g m)) (by simp [hs'])
    have : r m = a := by
      simp only [r, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      rw [← ha, hl']
    rw [this, ha]
  have hrf : ∀ a, r (f a) = a := by
    intro a
    apply hf
    rw [hr, hfg, map_zero, sub_zero]
  have hφ : φ = (φ ∘ₗ f) ∘ₗ r + (φ ∘ₗ s) ∘ₗ g := by
    ext m
    simp [hr]
  have e1 : r ∘ₗ (φ ∘ₗ f) = α := by
    ext a
    simp only [LinearMap.comp_apply, h1, hrf]
  have e2 : g ∘ₗ (φ ∘ₗ s) = γ := by
    ext c
    simp only [LinearMap.comp_apply, h2, hs']
  calc LinearMap.trace k M φ
      = LinearMap.trace k M ((φ ∘ₗ f) ∘ₗ r) + LinearMap.trace k M ((φ ∘ₗ s) ∘ₗ g) := by
        rw [← map_add, ← hφ]
    _ = _ := by
        rw [LinearMap.trace_comp_comm' r (φ ∘ₗ f), LinearMap.trace_comp_comm' g (φ ∘ₗ s), e1, e2]

theorem trace_quotient_pow {k B : Type*} [Field k] [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) (e : ℕ)
    [Algebra k (B ⧸ P ^ (e + 1))] [Algebra k (B ⧸ P)] [Module.Finite k (B ⧸ P ^ (e + 1))]
    (h : ∀ c : k, Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero e))
      (algebraMap k (B ⧸ P ^ (e + 1)) c) = algebraMap k (B ⧸ P) c) (x : B) :
    Algebra.trace k (B ⧸ P ^ (e + 1)) (Ideal.Quotient.mk _ x) =
      (e + 1 : k) * Algebra.trace k (B ⧸ P) (Ideal.Quotient.mk _ x) := by
  rename_i hmax instA instP instF
  revert h instF instA
  induction e with
  | zero =>
    intro instA instF h
    have hbij : Function.Bijective
        (Ideal.Quotient.factor (Ideal.pow_le_self (I := P) (Nat.succ_ne_zero 0))) := by
      refine ⟨?_, Ideal.Quotient.factor_surjective _⟩
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa using hy
    let g : (B ⧸ P ^ (0 + 1)) →ₐ[k] B ⧸ P :=
      { toRingHom := Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero 0))
        commutes' := h }
    have := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective g hbij) (Ideal.Quotient.mk _ x)
    rw [← this]
    simp [g]
  | succ e ih =>
    intro instA instF h
    have hle : P ^ (e + 1 + 1) ≤ P ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    let instB : Algebra k (B ⧸ P ^ (e + 1)) :=
      ((Ideal.Quotient.factor hle).comp (algebraMap k (B ⧸ P ^ (e + 1 + 1)))).toAlgebra
    let g : (B ⧸ P ^ (e + 1 + 1)) →ₐ[k] B ⧸ P ^ (e + 1) :=
      { toRingHom := Ideal.Quotient.factor hle
        commutes' := fun _ => rfl }
    have hgmk : ∀ y : B, g (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y := fun _ => rfl
    have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hle
    have instG : Module.Finite k (B ⧸ P ^ (e + 1)) := Module.Finite.of_surjective g.toLinearMap hg
    have ih' := @ih instB instG (by
      intro c
      rw [← h c]
      change Ideal.Quotient.factor _ (Ideal.Quotient.factor hle (algebraMap k _ c)) = _
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (algebraMap k (B ⧸ P ^ (e + 1 + 1)) c)
      rw [← hz]
      rfl)
    obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP hmax.ne_top (e + 1)
    let f0 : (B ⧸ P) →ₗ[B] B ⧸ P ^ (e + 1 + 1) :=
      Submodule.mapQ P (P ^ (e + 1 + 1) : Ideal B) (LinearMap.mul B B a) (by
        intro y hy
        change a * y ∈ P ^ (e + 1 + 1)
        rw [pow_succ P (e + 1)]
        exact Ideal.mul_mem_mul ha hy)
    have hf0 : ∀ y : B, f0 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (a * y) := fun _ => rfl
    let f : (B ⧸ P) →ₗ[k] B ⧸ P ^ (e + 1 + 1) :=
      { toFun := f0
        map_add' := f0.map_add
        map_smul' := by
          intro c y
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (algebraMap k (B ⧸ P ^ (e + 1 + 1)) c)
          rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, ← h c, ← hz,
            Ideal.Quotient.factor_mk, ← map_mul, hf0, hf0, ← map_mul]
          congr 1
          ring }
    have hf : ∀ y : B, f (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (a * y) := fun _ => rfl
    have key := trace_add_of_short_exact f g.toLinearMap ?_ hg ?_ ?_
      (Algebra.lmul k _ (Ideal.Quotient.mk _ x)) (Algebra.lmul k _ (Ideal.Quotient.mk _ x))
      (Algebra.lmul k _ (Ideal.Quotient.mk _ x)) ?_ ?_
    · rw [← Algebra.trace_apply, ← Algebra.trace_apply, ← Algebra.trace_apply] at key
      rw [key, ih']
      push_cast
      ring
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hf, Ideal.Quotient.eq_zero_iff_mem] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (Ideal.IsMaximal.mem_pow_mul P hy).resolve_left ha'
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hf, AlgHom.toLinearMap_apply, hgmk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ ha
    · intro m hm
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [AlgHom.toLinearMap_apply, hgmk, Ideal.Quotient.eq_zero_iff_mem] at hm
      have hsup : P ^ (e + 1 + 1) ⊔ Ideal.span {a} = P ^ (e + 1) := by
        refine Ideal.eq_prime_pow_of_succ_lt_of_le hP ?_ ?_
        · refine lt_of_le_of_ne le_sup_left fun hh => ha' ?_
          rw [hh]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
        · exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).2 ha)
      rw [← hsup] at hm
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hw
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [hf, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hu, zero_add, mul_comm]
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk _ x * f (Ideal.Quotient.mk _ y) =
        f (Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ y)
      rw [← map_mul, hf, hf, ← map_mul]
      congr 1
      ring
    · intro m
      change g (Ideal.Quotient.mk _ x * m) = Ideal.Quotient.mk _ x * g m
      rw [map_mul, hgmk]

end GlobalTheory.TameDifferent

namespace GlobalTheory.TameDifferent

open nonZeroDivisors Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

theorem intTrace_mk_eq
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] (hP0 : P ≠ ⊥)
    (n : ℕ) (hPQ : IsCoprime P Q) (hP : P ^ (n + 1) * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hx : x ∈ Q) :
    Ideal.Quotient.mk p (Algebra.intTrace A B x) =
      ((n + 1 : ℕ) : A ⧸ p) * Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ x) := by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let : Algebra (A ⧸ p) (B ⧸ P ^ (n + 1)) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ (n + 1)) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ (n + 1)) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ (n + 1))
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P ^ (n + 1)) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans
        (Ideal.quotientMulEquivQuotientProd _ Q hPQ.pow_left),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  have hx'' : (e (Ideal.Quotient.mk _ x)).1 = Ideal.Quotient.mk _ x := by
    simp [e]
  let := Ideal.Quotient.field p
  rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e,
    Algebra.trace_prod_apply, hx', hx'', map_zero, add_zero, Nat.cast_add, Nat.cast_one]
  refine trace_quotient_pow P hP0 n ?_ x
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

theorem not_pow_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (hP0 : P ≠ ⊥)
    (n : ℕ) (hPQ : IsCoprime P Q) (hP : P ^ (n + 1) * Q = Ideal.map (algebraMap A B) p)
    (hn : ((n + 1 : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ (n + 1) ∣ differentIdeal A B := by
  intro h
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field P
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (A ⧸ p) (B ⧸ P) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : x ∈ P ⊔ Q := by
    rw [Ideal.isCoprime_iff_sup_eq.mp hPQ]; trivial
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp h1
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_add] at hx
  refine not_dvd_differentIdeal_of_intTrace_not_mem A _ Q hP y hy ?_ h
  rw [← Ideal.Quotient.eq_zero_iff_mem, intTrace_mk_eq P Q hP0 n hPQ hP y hy]
  exact mul_ne_zero hn hx

end GlobalTheory.TameDifferent

namespace GlobalTheory.TameDifferent

open nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem pow_dvd_differentIdeal_iff_pow_succ_dvd_map : ∀ (A B : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [CharZero (IsLocalRing.ResidueField A)] (Q : Ideal B) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] (n : ℕ),
    Q ^ n ∣ differentIdeal A B ↔ Q ^ (n + 1) ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  intro A B _ _ _ _ _ _ _ _ _ Q _ _ n
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hm' : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hm
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hm Q
  obtain ⟨R, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hm' Q
  set e := Multiset.count Q
    (UniqueFactorizationMonoid.normalizedFactors ((IsLocalRing.maximalIdeal A).map (algebraMap A B)))
  have hQm : Q ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  have hk : ∀ k, Q ^ k ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) ↔ k ≤ e := by
    intro k
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      have h3 : Q ^ e * Q ∣ Q ^ e * R := by
        rw [← pow_succ, ← h₂]
        exact (pow_dvd_pow Q hlt).trans h
      have h4 : Q ∣ R := (mul_dvd_mul_iff_left (pow_ne_zero _ hQ0)).mp h3
      have h5 : R ≤ Q := Ideal.dvd_iff_le.mp h4
      apply (Ideal.IsMaximal.ne_top ‹Q.IsMaximal›)
      rw [← h₁]
      exact le_antisymm le_sup_left (sup_le le_rfl h5)
    · intro h
      rw [h₂]
      exact (pow_dvd_pow Q h).trans (dvd_mul_right _ _)
  have he : e ≠ 0 := by
    have := (hk 1).mp (by simpa using hQm)
    omega
  obtain ⟨k, hke⟩ := Nat.exists_eq_succ_of_ne_zero he
  have : CharZero A := RingHom.charZero (IsLocalRing.residue A)
  have : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := inferInstance
  have hc : CharZero (A ⧸ IsLocalRing.maximalIdeal A) :=
    inferInstanceAs (CharZero (IsLocalRing.ResidueField A))
  have : Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
    let := Ideal.Quotient.field Q
    infer_instance
  have hD1 : Q ^ (e - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal A Q e hm ((hk e).mpr le_rfl)
  have hD2 : ¬ Q ^ e ∣ differentIdeal A B := by
    rw [hke]
    refine not_pow_dvd_differentIdeal (p := IsLocalRing.maximalIdeal A) Q R hQ0 k (Ideal.isCoprime_iff_sup_eq.mpr h₁) ?_ ?_
    · rw [h₂, hke]
    · exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [hk (n + 1)]
  constructor
  · intro h
    by_contra hlt
    exact hD2 ((pow_dvd_pow Q (by omega)).trans h)
  · intro h
    exact (pow_dvd_pow Q (by omega)).trans hD1

end GlobalTheory.TameDifferent
