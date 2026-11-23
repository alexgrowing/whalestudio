import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom

namespace GlobalTheory

open IsLocalRing

section Affine

theorem finiteType_int_of_finiteType (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType A B] : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]

theorem exists_padic_point_norm_lt (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    {b c f : A} (hc : c ≠ 0) (hf : f ≠ 0) (h : ∀ s ∉ m, ¬ c ∣ s * b) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : A →+* integralClosure ℤ_[p] K,
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 ∧
            ‖((y c : K) : PadicAlgCl p)‖ < ‖((y b : K) : PadicAlgCl p)‖ := by
  have hm := (inferInstance : m.IsMaximal).ne_top
  have h1m : (1 : A) ∉ m := (Ideal.ne_top_iff_one m).mp hm
  have hb : b ≠ 0 := by
    rintro rfl
    exact h 1 h1m (by simp)
  haveI : IsDomain L := IsLocalization.isDomain_of_atPrime L m
  let F := FractionRing L
  have hinj : Function.Injective (algebraMap A F) := by
    rw [IsScalarTower.algebraMap_eq A L F]
    exact (IsFractionRing.injective L F).comp
      (IsLocalization.injective L m.primeCompl_le_nonZeroDivisors)
  have hne : ∀ {x : A}, x ≠ 0 → algebraMap A F x ≠ 0 := fun hx h0 =>
    hx (hinj (h0.trans (map_zero _).symm))
  set ψ : F := algebraMap A F c / algebraMap A F b with hψ
  have hψ0 : ψ ≠ 0 := div_ne_zero (hne hc) (hne hb)
  let B := Algebra.adjoin A {ψ}
  let ψ' : B := ⟨ψ, Algebra.subset_adjoin rfl⟩
  have hJ : m.map (algebraMap A B) ⊔ Ideal.span {ψ'} ≠ ⊤ := by
    intro heq
    letI := invertibleOfNonzero hψ0
    obtain ⟨q, hq, hqx⟩ :=
      Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top ψ _ hm heq
    have hs : q.leadingCoeff ∉ m := fun h' => h1m (by simpa using sub_mem h' hq)
    have hint : IsIntegral L (q.leadingCoeff • ⅟ψ) :=
      (isIntegral_leadingCoeff_smul q _ hqx).tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj m.primeCompl z
    refine h (t * q.leadingCoeff) (m.primeCompl.mul_mem t.2 hs) ⟨a, hinj ?_⟩
    have e := congrArg (algebraMap L F) hat
    rw [map_mul, hz, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      invOf_eq_inv, hψ, inv_div, Algebra.smul_def] at e
    simp only [map_mul] at e ⊢
    rw [div_eq_mul_inv] at e
    linear_combination algebraMap A F c * e - algebraMap A F t * algebraMap A F q.leadingCoeff *
      algebraMap A F b * mul_inv_cancel₀ (hne hc)
  obtain ⟨m₁, hm₁, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hinjB : Function.Injective (algebraMap A B) := fun x x' e => hinj (congrArg Subtype.val e)
  haveI : CharZero B := charZero_of_injective_algebraMap hinjB
  haveI : Algebra.FiniteType A B := .adjoin_of_finite (Set.finite_singleton ψ)
  haveI := finiteType_int_of_finiteType A B
  have hcom : m₁.comap (algebraMap A B) = m :=
    ((inferInstance : m.IsMaximal).eq_of_le (Ideal.comap_ne_top _ hm₁.ne_top)
      (Ideal.map_le_iff_le_comap.mp (le_sup_left.trans hle))).symm
  obtain ⟨K₀, hK₀, H⟩ := exists_padic_point_forall_ge (p := p) m₁
    (by rw [← map_natCast (algebraMap A B), ← Ideal.mem_comap, hcom]; exact hp)
    (f := algebraMap A B (f * b))
    (fun h0 => mul_ne_zero hf hb (hinjB (h0.trans (map_zero _).symm)))
  refine ⟨K₀, hK₀, fun K _ hK => ?_⟩
  obtain ⟨y, hy, hyf⟩ := H K hK
  rw [map_mul, map_mul] at hyf
  refine ⟨y.comp (algebraMap A B), by rw [← Ideal.comap_comap, hy, hcom],
    left_ne_zero_of_mul hyf, ?_⟩
  have hψm : y ψ' ∈ maximalIdeal (integralClosure ℤ_[p] K) := by
    rw [← Ideal.mem_comap, hy]
    exact hle (Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [mem_maximalIdeal_integralClosure_iff] at hψm
  have e : algebraMap A B c = ψ' * algebraMap A B b :=
    Subtype.ext (div_mul_cancel₀ _ (hne hb)).symm
  have hb' : ((y (algebraMap A B b) : K) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hyf
  simp only [RingHom.comp_apply]
  rw [e, map_mul]
  push_cast
  rw [norm_mul]
  exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hb') hψm

theorem exists_notMem_dvd_mul_of_forall_norm_le (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    {b c f : A} (hc : c ≠ 0) (hf : f ≠ 0)
    (h : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
      (y : A →+* integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m → y f ≠ 0 →
        ‖((y b : K) : PadicAlgCl p)‖ ≤ ‖((y c : K) : PadicAlgCl p)‖) :
    ∃ s ∉ m, c ∣ s * b := by
  by_contra hn
  push Not at hn
  obtain ⟨K, hK, H⟩ := exists_padic_point_norm_lt m hp L hc hf hn
  obtain ⟨y, h1, h2, h3⟩ := H K le_rfl
  exact absurd (h K y h1 h2) (not_le.mpr h3)

omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] in

theorem isUnit_val_comp_of_ne_zero {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (y : A →+* integralClosure ℤ_[p] K) {a : A} (h : y a ≠ 0) :
    IsUnit ((algebraMap (integralClosure ℤ_[p] K) K).comp y a) :=
  IsUnit.mk0 _ fun h0 => h (Subtype.ext h0)

variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]

theorem exists_padic_point_one_lt_norm (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) {f : A} (hf : f ≠ 0) {φ : S}
    (h : ∀ s ∉ m, ∀ b : A, algebraMap A S s * φ ≠ algebraMap A S b) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 ∧
            1 < ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
              PadicAlgCl p)‖ := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a φ
  obtain ⟨K₀, hK₀, H⟩ := exists_padic_point_norm_lt (b := b) m hp L (pow_ne_zero n ha)
    (mul_ne_zero ha hf) (by
      rintro s hs ⟨d, hd⟩
      refine h s hs d (((IsLocalization.Away.algebraMap_isUnit (S := S) a).pow n).mul_left_cancel ?_)
      rw [← map_pow, ← map_mul, ← hd, map_mul, ← hb, map_pow]
      ring)
  refine ⟨K₀, hK₀, fun K _ hK => ?_⟩
  obtain ⟨y, h1, h2, h3⟩ := H K hK
  rw [map_mul] at h2
  refine ⟨y, left_ne_zero_of_mul h2, h1, right_ne_zero_of_mul h2, ?_⟩
  set v := IsLocalization.Away.lift (S := S) a
    (isUnit_val_comp_of_ne_zero y (left_ne_zero_of_mul h2))
  have e : v φ * (y (a ^ n) : K) = (y b : K) := by
    have := congrArg v hb
    rw [map_mul, ← map_pow, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
    exact this
  rw [← e, IntermediateField.coe_mul, norm_mul] at h3
  by_contra hn
  exact absurd h3 (not_lt.mpr (mul_le_of_le_one_left (norm_nonneg _) (not_lt.mp hn)))

theorem exists_notMem_mul_eq_of_forall_norm_le_one (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) {φ : S}
    (h : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
      (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
        ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1) :
    ∃ s ∉ m, ∃ b : A, algebraMap A S s * φ = algebraMap A S b := by
  by_contra hn
  push Not at hn
  obtain ⟨K, hK, H⟩ := exists_padic_point_one_lt_norm m hp L ha one_ne_zero hn
  obtain ⟨y, h1, h2, -, h3⟩ := H K le_rfl
  exact absurd (h K y h1 h2) (not_le.mpr h3)

omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] [IsLocalization.Away a S] in

theorem algebraMap_mem_range_atPrime_iff (a : A) [IsLocalization.Away a S] (m : Ideal A) [m.IsPrime]
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m]
    (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F] [Algebra L F]
    [IsScalarTower A S F] [IsScalarTower A L F] (φ : S) :
    algebraMap S F φ ∈ (algebraMap L F).range ↔
      ∃ s ∉ m, ∃ b : A, algebraMap A S s * φ = algebraMap A S b := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj m.primeCompl z
    have hinj : Function.Injective (algebraMap S F) :=
      IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers a) S _ fun x hx => by
        rw [← IsScalarTower.algebraMap_apply] at hx
        rw [(FaithfulSMul.algebraMap_eq_zero_iff A F).mp hx, map_zero]
    refine ⟨s, s.2, b, hinj ?_⟩
    have e := congrArg (algebraMap L F) hbs
    rw [map_mul, hz, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, mul_comm, e]
  · rintro ⟨s, hs, b, hb⟩
    refine ⟨IsLocalization.mk' L b (⟨s, hs⟩ : m.primeCompl), ?_⟩
    have hs0 : algebraMap A F s ≠ 0 := by
      rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      rintro rfl
      exact hs m.zero_mem
    refine mul_left_cancel₀ hs0 ?_
    have e := congrArg (algebraMap S F) hb
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e
    rw [e, IsScalarTower.algebraMap_apply A L F s, ← map_mul, IsScalarTower.algebraMap_apply A L F b]
    exact congrArg _ (IsLocalization.mk'_spec' L b (⟨s, hs⟩ : m.primeCompl))

theorem mem_range_atPrime_of_forall_norm_le_one (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F]
    [Algebra L F] [IsScalarTower A S F] [IsScalarTower A L F] {φ : S}
    (h : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
      (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
        ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1) :
    algebraMap S F φ ∈ (algebraMap L F).range :=
  (algebraMap_mem_range_atPrime_iff a m L F φ).mpr
    (exists_notMem_mul_eq_of_forall_norm_le_one m hp L ha h)

omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] in

theorem norm_le_one_of_mul_eq {m : Ideal A} {φ : S} {s b : A} (hs : s ∉ m)
    (hb : algebraMap A S s * φ = algebraMap A S b)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0)
    (hy : (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m) :
    ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1 := by
  set v := IsLocalization.Away.lift (S := S) a (isUnit_val_comp_of_ne_zero y hya)
  have e : (y s : K) * v φ = (y b : K) := by
    have := congrArg v hb
    rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at this
    exact this
  rw [← hy, Ideal.mem_comap, mem_maximalIdeal_integralClosure_iff, not_lt] at hs
  have h1 := (mem_integralClosure_padicInt_iff K _).mp (y b).2
  rw [← e, IntermediateField.coe_mul, norm_mul] at h1
  exact (le_mul_of_one_le_left (norm_nonneg _) hs).trans h1

theorem mem_range_atPrime_iff_forall_norm_le_one (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F]
    [Algebra L F] [IsScalarTower A S F] [IsScalarTower A L F] (φ : S) :
    algebraMap S F φ ∈ (algebraMap L F).range ↔
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
        (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
          ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
            PadicAlgCl p)‖ ≤ 1 := by
  refine ⟨fun h K _ y hya hy => ?_, mem_range_atPrime_of_forall_norm_le_one m hp L ha F⟩
  obtain ⟨s, hs, b, hb⟩ := (algebraMap_mem_range_atPrime_iff a m L F φ).mp h
  exact norm_le_one_of_mul_eq hs hb K y hya hy

theorem mem_range_of_forall_norm_le_one [IsIntegrallyClosed A] (ha : a ≠ 0) {φ : S}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1) :
    φ ∈ (algebraMap A S).range := by
  let I : Ideal A := (Submodule.span A {(1 : S)}).comap (LinearMap.toSpanSingleton A S φ)
  have hI : ∀ s, s ∈ I ↔ ∃ b, algebraMap A S s * φ = algebraMap A S b := fun s => by
    simp [I, Submodule.mem_span_singleton, Algebra.smul_def, eq_comm]
  have : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨q, hq, hqm⟩ := exists_prime_natCast_mem_of_finiteType_int m
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsIntegrallyClosed (Localization.AtPrime m) :=
      isIntegrallyClosed_of_isLocalization _ _ m.primeCompl_le_nonZeroDivisors
    obtain ⟨s, hs, hb⟩ := exists_notMem_mul_eq_of_forall_norm_le_one m hqm
      (Localization.AtPrime m) ha (φ := φ) fun K _ y hya _ => h q K y hya
    exact hs (hle ((hI s).mpr hb))
  obtain ⟨b, hb⟩ := (hI 1).mp (this ▸ Submodule.mem_top)
  exact ⟨b, by simpa using hb.symm⟩

end Affine

section Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y

theorem top_le_preimage_iff_genericPoint_mem {O K : Type} [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [FaithfulSMul O K] {Z : Scheme.{0}} (y : Spec (.of O) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ y) ⁻¹ᵁ U ↔ y (genericPoint _) ∈ U := by
  have key : ∀ q : Spec (.of K), (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ y) q =
      y (genericPoint _) := fun q => by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_bot_of_affine]
    refine congrArg y (PrimeSpectrum.ext ?_)
    rw [Subsingleton.elim q (⊥ : PrimeSpectrum K)]
    exact Ideal.comap_bot_of_injective (algebraMap O K) (FaithfulSMul.algebraMap_injective O K)
  refine ⟨fun h => ?_, fun h q _ => ?_⟩
  · rw [← key (⊥ : PrimeSpectrum K)]
    exact h (Set.mem_univ _)
  · rw [← key q] at h
    exact h

theorem exists_germToFunctionField_eq_of_mem_range_stalk {Z : Scheme.{0}} [IsIntegral Z]
    {t : Z.functionField} {x : Z}
    (h : t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) {W : Z.Opens} (hx : x ∈ W) :
    ∃ (V : Z.Opens) (_ : Nonempty V) (s : Γ(Z, V)),
      x ∈ V ∧ V ≤ W ∧ Z.germToFunctionField V s = t := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨V, hV, s, rfl⟩ := Z.presheaf.exists_germ_eq g
  haveI : Nonempty V := ⟨⟨x, hV⟩⟩
  haveI : Nonempty (V ⊓ W : Z.Opens) := ⟨⟨x, hV, hx⟩⟩
  refine ⟨V ⊓ W, inferInstance, Z.presheaf.map (homOfLE inf_le_left).op s, ⟨hV, hx⟩,
    inf_le_right, ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact Z.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ s

theorem exists_germToFunctionField_eq_of_closedPoints {Z : Scheme.{0}} [IsIntegral Z]
    [JacobsonSpace Z] (W : Z.Opens) [Nonempty W] (t : Z.functionField)
    (h : ∀ x ∈ W, IsClosed ({x} : Set Z) →
      t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) :
    ∃ s : Γ(Z, W), Z.germToFunctionField W s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally W t fun x hx => ?_
  obtain ⟨z, ⟨hzx, hzW⟩, hz⟩ := nonempty_inter_closedPoints (Z := closure {x} ∩ (W : Set Z))
    ⟨x, subset_closure rfl, hx⟩ (isClosed_closure.isLocallyClosed.inter W.isOpen.isLocallyClosed)
  obtain ⟨V, hV, s, hzV, hVW, hs⟩ := exists_germToFunctionField_eq_of_mem_range_stalk
    (h z hzW hz) hzW
  exact ⟨V, hV, s, (specializes_iff_mem_closure.mpr hzx).mem_open V.isOpen hzV, hVW, hs⟩

theorem jacobsonSpace_of_finiteType_over_int {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ))
    [LocallyOfFiniteType π] : JacobsonSpace Z :=
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : JacobsonSpace (Spec (.of ℤ)) := inferInstanceAs (JacobsonSpace (PrimeSpectrum ℤ))
  LocallyOfFiniteType.jacobsonSpace π

variable {Z : Scheme.{0}} [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]

include π

theorem exists_padic_point_scheme_one_lt_norm {p : ℕ} [Fact p.Prime] {x : Z}
    (hx : IsClosed ({x} : Set Z)) (hp : (p : Z.residueField x) = 0)
    [IsIntegrallyClosed (Z.presheaf.stalk x)] {U : Z.Opens} [Nonempty U] (U' : Z.Opens)
    [Nonempty U'] {φ : Γ(Z, U)}
    (h : Z.germToFunctionField U φ ∉ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
          y (closedPoint (integralClosure ℤ_[p] K)) = x ∧ y (genericPoint _) ∈ U' ∧
            1 < ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI := finiteType_int_sections π hV
  haveI := charZero_sections_of_flat π hV
  haveI := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  have hg : ∀ (W : Z.Opens) [Nonempty W], genericPoint Z ∈ W := fun W h =>
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using h)
  obtain ⟨f, hfU, hxf⟩ := hV.exists_basicOpen_le (V := U ⊓ U') ⟨_, hg U, hg U'⟩ (hg V)
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hxf
  haveI : Nonempty (Z.basicOpen f) := ⟨⟨_, hxf⟩⟩
  letI : Algebra Γ(Z, V) (Z.presheaf.stalk x) := Z.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk x) Z.functionField :=
    functionField_isScalarTower Z V ⟨x, hxV⟩
  haveI := hV.isLocalization_basicOpen f
  haveI : IsScalarTower Γ(Z, V) Γ(Z, Z.basicOpen f) Z.functionField := .of_algebraMap_eq fun a =>
    (Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le f)) _ _ a).symm
  haveI : FaithfulSMul Γ(Z, V) Z.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (Z.germToFunctionField_injective V)
  let φ' : Γ(Z, Z.basicOpen f) := Z.presheaf.map (homOfLE (hfU.trans inf_le_left)).op φ
  have hφ' : algebraMap _ Z.functionField φ' = Z.germToFunctionField U φ :=
    Z.presheaf.germ_res_apply (homOfLE (hfU.trans inf_le_left)) _ _ φ
  rw [← hφ', algebraMap_mem_range_atPrime_iff f (hV.primeIdealOf ⟨x, hxV⟩).asIdeal] at h
  push Not at h
  obtain ⟨K₀, hK₀, H⟩ := exists_padic_point_one_lt_norm (p := p)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    ((mem_primeIdealOf_iff_evaluation_eq_zero hV hxV _).mpr (by simpa using hp))
    (Z.presheaf.stalk x) hf one_ne_zero h
  refine ⟨K₀, hK₀, fun K _ hK => ?_⟩
  obtain ⟨y, hyf, hy, -, hlt⟩ := H K hK
  let y' : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom y) ≫ hV.fromSpec
  have hgen : y' (genericPoint _) ∈ Z.basicOpen f := by
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen,
      genericPoint_eq_bot_of_affine]
    exact hyf
  have hD := (top_le_preimage_iff_genericPoint_mem (K := K) y' _).mpr hgen
  have hU := (top_le_preimage_iff_genericPoint_mem (K := K) y' U).mpr (hfU hgen).1
  refine ⟨y', hU, ?_, (hfU hgen).2, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    exact (congrArg hV.fromSpec (PrimeSpectrum.ext hy)).trans (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)
  · have e : IsLocalization.Away.lift f (isUnit_val_comp_of_ne_zero y hyf) =
        ((genericPt(p, K, y')).appLE (Z.basicOpen f) ⊤ hD ≫ (Scheme.ΓSpecIso (.of K)).hom).hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
      rw [IsLocalization.Away.lift_comp]
      have e1 : (genericPt(p, K, y')) = Spec.map (CommRingCat.ofHom
          ((algebraMap (integralClosure ℤ_[p] K) K).comp y)) ≫ hV.fromSpec := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      have e2 : ∀ (t : Spec (.of K) ⟶ Z) (ht : ⊤ ≤ t ⁻¹ᵁ Z.basicOpen f) (g : Γ(Z, V) ⟶ .of K),
          t = Spec.map g ≫ hV.fromSpec →
          g = Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op ≫ t.appLE (Z.basicOpen f) ⊤ ht ≫
            (Scheme.ΓSpecIso (.of K)).hom := by
        rintro t ht g rfl
        rw [Scheme.Hom.map_appLE_assoc, AffinePointValues.appLE_specMap_fromSpec]
      exact congrArg CommRingCat.Hom.hom (e2 _ hD _ e1)
    rw [e] at hlt
    have e3 := (genericPt(p, K, y')).map_appLE hD (homOfLE (hfU.trans inf_le_left)).op
    rw [← e3]
    exact hlt

theorem mem_range_stalk_of_forall_norm_le_one {p : ℕ} [Fact p.Prime] {x : Z}
    (hx : IsClosed ({x} : Set Z)) (hp : (p : Z.residueField x) = 0)
    [IsIntegrallyClosed (Z.presheaf.stalk x)] {U : Z.Opens} [Nonempty U] {φ : Γ(Z, U)}
    (h : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
      (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
      y (closedPoint (integralClosure ℤ_[p] K)) = x →
        ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
          PadicAlgCl p)‖ ≤ 1) :
    Z.germToFunctionField U φ ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range := by
  by_contra hn
  obtain ⟨K, hK, H⟩ := exists_padic_point_scheme_one_lt_norm π hx hp U hn
  obtain ⟨y, hy, h1, -, h2⟩ := H K le_rfl
  exact absurd (h K y hy h1) (not_le.mpr h2)

theorem exists_germToFunctionField_eq_of_frequently_norm_le_one {U : Z.Opens} [Nonempty U]
    (U' W : Z.Opens) [Nonempty U'] [Nonempty W]
    (hn : ∀ x ∈ W, x ∉ U → IsClosed ({x} : Set Z) → IsIntegrallyClosed (Z.presheaf.stalk x))
    {φ : Γ(Z, U)}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K₀], ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (_ : FiniteDimensional ℚ_[p] K), K₀ ≤ K ∧
      ∀ (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
        y (closedPoint (integralClosure ℤ_[p] K)) ∈ W →
        y (closedPoint (integralClosure ℤ_[p] K)) ∉ U → y (genericPoint _) ∈ U' →
        ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
          PadicAlgCl p)‖ ≤ 1) :
    ∃ ψ : Γ(Z, W), Z.germToFunctionField W ψ = Z.germToFunctionField U φ := by
  haveI := jacobsonSpace_of_finiteType_over_int π
  refine exists_germToFunctionField_eq_of_closedPoints W _ fun x hxW hx => ?_
  by_cases hxU : x ∈ U
  · exact ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField Z hxU φ⟩
  haveI := hn x hxW hxU hx
  obtain ⟨p, hp, hpx⟩ := exists_prime_residueField_eq_zero π hx
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨K₀, hK₀, H⟩ := exists_padic_point_scheme_one_lt_norm π hx hpx U' hne
  obtain ⟨K, hK, hle, H'⟩ := h p K₀
  obtain ⟨y, hy, h1, h2, h3⟩ := H K hle
  exact absurd (H' y hy (h1 ▸ hxW) (h1 ▸ hxU) h2) (not_le.mpr h3)

theorem exists_germToFunctionField_eq_of_forall_norm_le_one [IsNormalScheme Z] {U : Z.Opens}
    [Nonempty U] (W : Z.Opens) [Nonempty W] {φ : Γ(Z, U)}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z)
      (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U), y (closedPoint (integralClosure ℤ_[p] K)) ∈ W →
        ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
          PadicAlgCl p)‖ ≤ 1) :
    ∃ ψ : Γ(Z, W), Z.germToFunctionField W ψ = Z.germToFunctionField U φ :=
  exists_germToFunctionField_eq_of_frequently_norm_le_one π U W (fun _ _ _ _ => inferInstance)
    fun p _ K hK => ⟨K, hK, le_rfl, fun y hy hW _ _ => h p K y hy hW⟩

theorem existsUnique_extension_of_forall_norm_le_one [IsNormalScheme Z] {U : Z.Opens}
    [Nonempty U] {φ : Γ(Z, U)}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z)
      (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
        ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
          PadicAlgCl p)‖ ≤ 1) :
    ∃! ψ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op ψ = φ := by
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_germToFunctionField_eq_of_forall_norm_le_one π ⊤ (φ := φ)
    fun p _ K _ y hy _ => h p K y hy
  have e : Z.presheaf.map (homOfLE le_top).op ψ = φ :=
    Z.germToFunctionField_injective U
      ((Z.presheaf.germ_res_apply (homOfLE le_top) _ _ ψ).trans hψ)
  exact ⟨ψ, e, fun ψ' h' => map_injective_of_isIntegral Z (homOfLE le_top) (h'.trans e.symm)⟩

omit π [IsIntegral Z] [Flat π] [LocallyOfFiniteType π] in

theorem regular_of_forall_padic_point_norm_le_one :
    (∀ (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
      [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal], (p : A) ∈ m →
      IsIntegrallyClosed (Localization.AtPrime m) → ∀ a : A, a ≠ 0 → ∀ φ : Localization.Away a,
      (∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
        (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
          ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
            PadicAlgCl p)‖ ≤ 1) →
      ∃ s ∉ m, ∃ b : A, algebraMap A _ s * φ = algebraMap A _ b) ∧
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]
      (U : Z.Opens) [Nonempty U] (φ : Γ(Z, U)),
      (∀ (p : ℕ) [Fact p.Prime] (x : Z), IsClosed ({x} : Set Z) → (p : Z.residueField x) = 0 →
        IsIntegrallyClosed (Z.presheaf.stalk x) →
        (∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
          (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
          y (closedPoint (integralClosure ℤ_[p] K)) = x →
            ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ ≤ 1) →
        Z.germToFunctionField U φ ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) ∧
      (IsNormalScheme Z → ∀ (W : Z.Opens) [Nonempty W],
        (∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
          [FiniteDimensional ℚ_[p] K] (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z)
          (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U), y (closedPoint (integralClosure ℤ_[p] K)) ∈ W →
            ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ ≤ 1) →
        ∃ ψ : Γ(Z, W), Z.germToFunctionField W ψ = Z.germToFunctionField U φ) :=
  ⟨fun _ _ _ _ _ _ _ m _ hp _ _ ha _ h =>
      exists_notMem_mul_eq_of_forall_norm_le_one m hp (Localization.AtPrime m) ha h,
    fun _ _ π _ _ _ _ _ => ⟨fun _ _ _ hx hp _ h => mem_range_stalk_of_forall_norm_le_one π hx hp h,
      fun _ W _ h => exists_germToFunctionField_eq_of_forall_norm_le_one π W h⟩⟩

end Scheme

end GlobalTheory
