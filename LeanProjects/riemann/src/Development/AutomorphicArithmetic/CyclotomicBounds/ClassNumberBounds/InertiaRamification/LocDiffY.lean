import Mathlib

namespace KStar.Ram

section Helpers

open nonZeroDivisors Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem locDiffY_dvd_of_intTrace_mem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (hp : p ≠ ⊥) (P a : Ideal B) (ha : p.map (algebraMap A B) = P * a)
    (h : ∀ x ∈ a, Algebra.intTrace A B x ∈ p) : P ∣ differentIdeal A B := by
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
    apply inv_involutive.injective
    simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
    rw [div_self (by simpa), mul_one, inv_inv]
  rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hPbot, hP,
    Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
  rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
    ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
    FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
  simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hx
  intro y hy'
  obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
  obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
  have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
    rw [← Algebra.algebraMap_intTrace (A := A)]
    exact ⟨Algebra.intTrace A B z, h z hz, rfl⟩
  rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']

private theorem locDiffY_sep {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [IsTorsionFree A B] [Module.Finite A B] [CharZero A] :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  infer_instance

private theorem locDiffY_ne_bot {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsTorsionFree A B] [Module.Finite A B] [CharZero A] :
    differentIdeal A B ≠ ⊥ := by
  have := locDiffY_sep (A := A) (B := B)
  exact differentIdeal_ne_bot

private theorem locDiffY_iff {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsTorsionFree A B] [Module.Finite A B] [CharZero A]
    {p : Ideal A} (hp : p ≠ ⊥) (P a : Ideal B) (ha : P * a = p.map (algebraMap A B)) :
    P ∣ differentIdeal A B ↔ ∀ x ∈ a, Algebra.intTrace A B x ∈ p := by
  have := locDiffY_sep (A := A) (B := B)
  refine ⟨fun h x hx => ?_, locDiffY_dvd_of_intTrace_mem hp P a ha.symm⟩
  by_contra hc
  exact not_dvd_differentIdeal_of_intTrace_not_mem A P a ha x hx hc h

private theorem locDiffY_trace_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (I : Ideal A) (x : B) :
    Algebra.trace (A ⧸ I) (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk I (Algebra.trace A B x) := by
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I),
    ← Ideal.Quotient.algebraMap_eq I, Algebra.trace_apply A x, ← LinearMap.trace_baseChange,
    Algebra.trace_apply]
  congr 1
  have : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I) (Ideal.Quotient.mk _ x) =
      1 ⊗ₜ x := rfl
  rw [this]
  ext y
  simp

private theorem locDiffY_isLocalRing {A : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] {p : A} (hp : Prime p) (n : ℕ)
    [Nontrivial (A ⧸ Ideal.span {p ^ n})] : IsLocalRing (A ⧸ Ideal.span {p ^ n}) := by
  have key : ∀ a : A, ¬ p ∣ a → IsUnit (Ideal.Quotient.mk (Ideal.span {p ^ n}) a) := by
    intro a ha
    obtain ⟨u, v, huv⟩ := (hp.irreducible.coprime_iff_not_dvd.mpr ha).pow_left (m := n)
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {p ^ n})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-u, by rw [← huv]; ring⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_cases h : p ∣ a
  · right
    have := key (1 - a) fun h' => hp.not_dvd_one (by simpa using dvd_add h' h)
    simpa using this
  · exact Or.inl (key a h)

private theorem locDiffY_trace_prod {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (I : Ideal A) [IsLocalRing (A ⧸ I)] {Q₁ Q₂ : Ideal B}
    (hc : IsCoprime Q₁ Q₂) (hP : Q₁ * Q₂ = I.map (algebraMap A B))
    [Algebra (A ⧸ I) (B ⧸ Q₁)] [IsScalarTower A (A ⧸ I) (B ⧸ Q₁)] {x : B} (hx : x ∈ Q₂) :
    Ideal.Quotient.mk I (Algebra.trace A B x) =
      Algebra.trace (A ⧸ I) (B ⧸ Q₁) (Ideal.Quotient.mk Q₁ x) := by
  let : Algebra (A ⧸ I) (B ⧸ Q₂) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ I) (B ⧸ Q₂) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ I) (B ⧸ Q₂) := .of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ I) (B ⧸ Q₁) := .of_restrictScalars_finite A _ _
  let e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] ((B ⧸ Q₁) × B ⧸ Q₂) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd Q₁ Q₂ hc),
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        refine Prod.ext ?_ rfl
        exact IsScalarTower.algebraMap_apply A (A ⧸ I) (B ⧸ Q₁) a }
  have : Module.Free (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv
  have : Module.Free (A ⧸ I) ((B ⧸ Q₁) × B ⧸ Q₂) := .of_equiv e.toLinearEquiv
  have : Module.Projective (A ⧸ I) (B ⧸ Q₁) :=
    .of_split (LinearMap.inl _ _ (B ⧸ Q₂)) (LinearMap.fst _ _ _) (LinearMap.fst_comp_inl _ _ _)
  have : Module.Projective (A ⧸ I) (B ⧸ Q₂) :=
    .of_split (LinearMap.inr _ (B ⧸ Q₁) _) (LinearMap.snd _ _ _) (LinearMap.snd_comp_inr _ _ _)
  have : Module.Free (A ⧸ I) (B ⧸ Q₁) := Module.free_of_flat_of_isLocalRing
  have : Module.Free (A ⧸ I) (B ⧸ Q₂) := Module.free_of_flat_of_isLocalRing
  have h2 : (e (Ideal.Quotient.mk _ x)).2 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [← locDiffY_trace_mk, ← Algebra.trace_eq_of_algEquiv e, Algebra.trace_prod_apply, h2,
    map_zero, add_zero]
  rfl

end Helpers

section

variable {A B : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B]
  [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [CharZero A]

theorem dvd_differentIdeal_iff_trace {a : A} (ha : a ≠ 0) {I J : Ideal B}
    (h : I * J = Ideal.span {algebraMap A B a}) :
    I ∣ differentIdeal A B ↔ ∀ x ∈ J, a ∣ Algebra.trace A B x := by
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  rw [locDiffY_iff (p := Ideal.span {a}) (by simpa using ha) I J
    (by rw [h, Ideal.map_span, Set.image_singleton]), Algebra.intTrace_eq_trace]
  simp only [Ideal.mem_span_singleton]

omit [CharZero A] in

theorem mk_trace_eq_trace_quotient {p : A} (hp : Prime p) (n : ℕ) {Q₁ Q₂ : Ideal B}
    (hc : IsCoprime Q₁ Q₂) (h : Q₁ * Q₂ = Ideal.span {algebraMap A B (p ^ n)})
    [Algebra (A ⧸ Ideal.span {p ^ n}) (B ⧸ Q₁)]
    [IsScalarTower A (A ⧸ Ideal.span {p ^ n}) (B ⧸ Q₁)] {x : B} (hx : x ∈ Q₂) :
    Ideal.Quotient.mk (Ideal.span {p ^ n}) (Algebra.trace A B x) =
      Algebra.trace (A ⧸ Ideal.span {p ^ n}) (B ⧸ Q₁) (Ideal.Quotient.mk Q₁ x) := by
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  rcases subsingleton_or_nontrivial (A ⧸ Ideal.span {p ^ n}) with hs | hs
  · exact Subsingleton.elim _ _
  have := locDiffY_isLocalRing hp n
  exact locDiffY_trace_prod _ hc (by rw [h, Ideal.map_span, Set.image_singleton]) hx

omit [IsPrincipalIdealRing A] [Module.Finite A B] [CharZero A] in
private theorem locDiffY_span_ne {p : A} (hp : p ≠ 0) :
    (Ideal.span {p}).map (algebraMap A B) ≠ ⊥ := by
  rw [ne_eq, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)]
  simpa using hp

omit [IsPrincipalIdealRing A] [Module.Finite A B] [CharZero A] in
private theorem locDiffY_P_ne {p : A} (hp : p ≠ 0) (P : Ideal B) [P.LiesOver (Ideal.span {p})] :
    P ≠ ⊥ :=
  ne_bot_of_le_ne_bot (locDiffY_span_ne hp)
    (Ideal.map_le_of_le_comap (P.over_def (Ideal.span {p})).le)

omit [IsPrincipalIdealRing A] [Module.Finite A B] [CharZero A] in
private theorem locDiffY_decomp {p : A} (hp : p ≠ 0) (P : Ideal B) [P.IsPrime]
    [P.LiesOver (Ideal.span {p})] (n : ℕ) :
    ∃ Q : Ideal B, IsCoprime P Q ∧
      P ^ (n * P.ramificationIdx A) * Q = Ideal.span {algebraMap A B (p ^ n)} := by
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (locDiffY_P_ne hp P)
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime (locDiffY_span_ne (B := B) hp) P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _
    (locDiffY_span_ne hp)] at h₂
  refine ⟨Q ^ n, (Ideal.isCoprime_iff_sup_eq.mpr h₁).pow_right, ?_⟩
  rw [mul_comm n, pow_mul, ← mul_pow, ← h₂, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, map_pow]

theorem pow_dvd_differentIdeal_iff_trace_quotient {p : A} (hp : Prime p) (P : Ideal B) [P.IsPrime]
    [P.LiesOver (Ideal.span {p})] {n k : ℕ} (hk : k ≤ n * P.ramificationIdx A)
    [Algebra (A ⧸ Ideal.span {p ^ n}) (B ⧸ P ^ (n * P.ramificationIdx A))]
    [IsScalarTower A (A ⧸ Ideal.span {p ^ n}) (B ⧸ P ^ (n * P.ramificationIdx A))] :
    P ^ k ∣ differentIdeal A B ↔ ∀ x ∈ P ^ (n * P.ramificationIdx A - k),
      Algebra.trace (A ⧸ Ideal.span {p ^ n}) (B ⧸ P ^ (n * P.ramificationIdx A))
        (Ideal.Quotient.mk _ x) = 0 := by
  obtain ⟨Q, hc, hQ⟩ := locDiffY_decomp hp.ne_zero P n
  have hc' : IsCoprime (P ^ (n * P.ramificationIdx A)) Q := hc.pow_left
  rw [dvd_differentIdeal_iff_trace (a := p ^ n) (pow_ne_zero _ hp.ne_zero)
    (J := P ^ (n * P.ramificationIdx A - k) * Q)
    (by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk, hQ])]
  constructor
  · intro H x hx
    obtain ⟨u, hu, w, hw, huw⟩ := Ideal.isCoprime_iff_exists.mp hc'
    have h1 : Ideal.Quotient.mk (P ^ (n * P.ramificationIdx A)) x =
        Ideal.Quotient.mk _ (x * w) := by
      rw [Ideal.Quotient.eq]
      have : x - x * w = x * u := by linear_combination (-x) * huw
      rw [this]
      exact Ideal.mul_mem_left _ _ hu
    rw [h1, ← mk_trace_eq_trace_quotient hp n hc' hQ (Ideal.mul_mem_left _ _ hw),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact H _ (Ideal.mul_mem_mul hx hw)
  · intro H x hx
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      mk_trace_eq_trace_quotient hp n hc' hQ (Ideal.mul_le_right hx)]
    exact H x (Ideal.mul_le_left hx)

end

private theorem locDiffY_bij {B B' : Type*} [CommRing B] [CommRing B'] (g : B →+* B')
    {I : Ideal B} {J : Ideal B'} (h : J.comap g = I) (hs : ∀ y, ∃ x, y - g x ∈ J) :
    Function.Bijective (Ideal.quotientMap J g h.ge) := by
  refine ⟨Ideal.quotientMap_injective' h.le, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨Ideal.Quotient.mk _ x, by rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq]; exact hx⟩

theorem multiplicity_differentIdeal_eq_of_quotient {A B A' B' : Type*}
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [CharZero A]
    [CommRing A'] [IsDomain A'] [IsPrincipalIdealRing A'] [CommRing B'] [IsDedekindDomain B']
    [Algebra A' B'] [Module.IsTorsionFree A' B'] [Module.Finite A' B'] [CharZero A']
    (f : A →+* A') (g : B →+* B') (hfg : g.comp (algebraMap A B) = (algebraMap A' B').comp f)
    {p : A} (hp : Prime p) (hp' : Prime (f p)) (P : Ideal B) (P' : Ideal B') [P.IsPrime]
    [P'.IsPrime] [P.LiesOver (Ideal.span {p})] [P'.LiesOver (Ideal.span {f p})]
    (hf : ∀ (n : ℕ) (y : A'), ∃ x : A, f p ^ n ∣ y - f x)
    (hf' : ∀ (n : ℕ) (x : A), f p ^ n ∣ f x → p ^ n ∣ x)
    (hg : ∀ (n : ℕ) (y : B'), ∃ x : B, y - g x ∈ P' ^ n)
    (hg' : ∀ n : ℕ, (P' ^ n).comap g = P ^ n) :
    P.ramificationIdx A = P'.ramificationIdx A' ∧ P.inertiaDeg A = P'.inertiaDeg A' ∧
      multiplicity P (differentIdeal A B) = multiplicity P' (differentIdeal A' B') := by
  have hfg' : ∀ a, g (algebraMap A B a) = algebraMap A' B' (f a) := fun a => congr($hfg a)
  have hP0 := locDiffY_P_ne hp.ne_zero P
  have hP0' := locDiffY_P_ne hp'.ne_zero P'
  have he : P.ramificationIdx A = P'.ramificationIdx A' := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {p}) P
      (locDiffY_span_ne hp.ne_zero),
      Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {f p}) P'
      (locDiffY_span_ne hp'.ne_zero)]
    refine multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_emultiplicity_iff.mpr fun m => ?_)
    simp only [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    rw [← hg', Ideal.mem_comap, hfg']
  have hfc : ∀ n : ℕ, (Ideal.span {f p ^ n}).comap f = Ideal.span {p ^ n} := by
    intro n
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    exact ⟨hf' n x, fun h => by simpa using map_dvd f h⟩
  refine ⟨he, ?_, ?_⟩
  · have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    have : P'.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0'
    have : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have : (Ideal.span {f p}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {p}) P,
      Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {f p}) P']
    have h1 : (Ideal.span {f p}).comap f = Ideal.span {p} := by simpa using hfc 1
    have h2 : P'.comap g = P := by simpa using hg' 1
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.ofBijective _ (locDiffY_bij f h1 fun y => by
        simpa [Ideal.mem_span_singleton] using hf 1 y))
      (RingEquiv.ofBijective _ (locDiffY_bij g h2 fun y => by simpa using hg 1 y)) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact congrArg (Ideal.Quotient.mk P') (hfg' a).symm
  · refine multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_emultiplicity_iff.mpr fun k => ?_)
    obtain ⟨Q, -, hQ⟩ := locDiffY_decomp hp.ne_zero P k
    obtain ⟨Q', -, hQ'⟩ := locDiffY_decomp hp'.ne_zero P' k
    have he0 : 0 < P.ramificationIdx A := Ideal.ramificationIdx_pos _ _
    have hk : k ≤ k * P.ramificationIdx A := Nat.le_mul_of_pos_right _ he0
    let : Algebra (A ⧸ Ideal.span {p ^ k}) (B ⧸ P ^ (k * P.ramificationIdx A)) :=
      Ideal.Quotient.algebraQuotientOfLEComap (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton, ← hQ]
        exact Ideal.mul_le_left)
    have : IsScalarTower A (A ⧸ Ideal.span {p ^ k}) (B ⧸ P ^ (k * P.ramificationIdx A)) :=
      .of_algebraMap_eq' rfl
    let : Algebra (A' ⧸ Ideal.span {f p ^ k}) (B' ⧸ P' ^ (k * P'.ramificationIdx A')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton, ← hQ']
        exact Ideal.mul_le_left)
    have : IsScalarTower A' (A' ⧸ Ideal.span {f p ^ k})
        (B' ⧸ P' ^ (k * P'.ramificationIdx A')) := .of_algebraMap_eq' rfl
    rw [pow_dvd_differentIdeal_iff_trace_quotient hp P hk,
      pow_dvd_differentIdeal_iff_trace_quotient hp' P' (n := k) (he ▸ hk)]
    have h2 : (P' ^ (k * P'.ramificationIdx A')).comap g = P ^ (k * P.ramificationIdx A) := by
      rw [hg', he]
    have key : ∀ x : B, Algebra.trace (A ⧸ Ideal.span {p ^ k})
        (B ⧸ P ^ (k * P.ramificationIdx A)) (Ideal.Quotient.mk _ x) = 0 ↔
        Algebra.trace (A' ⧸ Ideal.span {f p ^ k}) (B' ⧸ P' ^ (k * P'.ramificationIdx A'))
          (Ideal.Quotient.mk _ (g x)) = 0 := by
      intro x
      rw [Algebra.trace_eq_of_equiv_equiv
        (RingEquiv.ofBijective _ (locDiffY_bij f (hfc k) fun y => by
          simpa [Ideal.mem_span_singleton] using hf k y))
        (RingEquiv.ofBijective _ (locDiffY_bij g h2 (hg _)))
        (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
          congrArg (Ideal.Quotient.mk _) (hfg' a).symm)), map_eq_zero_iff _ (RingEquiv.injective _)]
      rfl
    constructor
    · intro H y hy
      obtain ⟨x, hx⟩ := hg (k * P'.ramificationIdx A') y
      rw [Ideal.Quotient.eq.mpr hx, ← key]
      apply H
      rw [← hg', Ideal.mem_comap, he]
      have := Ideal.sub_mem _ hy (Ideal.pow_le_pow_right (Nat.sub_le _ k) hx)
      simpa using this
    · intro H x hx
      rw [key]
      apply H
      rw [← he, ← Ideal.mem_comap, hg']
      exact hx

end KStar.Ram
