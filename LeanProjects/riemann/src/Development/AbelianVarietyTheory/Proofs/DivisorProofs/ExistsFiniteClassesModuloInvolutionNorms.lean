import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdNonnegOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedEqRepMulNormMulFixedUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFixedUnitsModFixedSquares
open NumberField IsDedekindDomain GlobalTheory.FixNormCls GlobalTheory.LocalDivisor
open scoped TensorProduct Classical

namespace GlobalTheory.FixNormField

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem finite_heightOneSpectrum_containing_finset_nat (K : Type) [Field K] [NumberField K] (S : Finset ℕ) :
    {P : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ S, ℓ ≠ 0 ∧ (ℓ : 𝓞 K) ∈ P.asIdeal}.Finite := by
  have : {P : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ S, ℓ ≠ 0 ∧ (ℓ : 𝓞 K) ∈ P.asIdeal} ⊆
      ⋃ ℓ ∈ S.filter (· ≠ 0), {P | P.asIdeal ∣ Ideal.span {(ℓ : 𝓞 K)}} := by
    rintro P ⟨ℓ, hS, h0, hP⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter]
    exact ⟨ℓ, ⟨hS, h0⟩, Ideal.dvd_span_singleton.2 hP⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun ℓ hℓ => ?_) this
  refine Ideal.finite_factors ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast (Finset.mem_filter.1 hℓ).2

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_finset_submodule_eq_add_two_smul {M : Type*} [AddCommGroup M]
    [Module.Finite ℤ M] (N : Submodule ℤ M) :
    ∃ V : Finset M, (∀ v ∈ V, v ∈ N) ∧ ∀ h ∈ N, ∃ v ∈ V, ∃ w ∈ N, h = v + 2 • w := by
  classical
  haveI := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  haveI : Module.Finite ℤ N := Module.IsNoetherian.finite ℤ N
  let D : Submodule ℤ N := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Finite (N ⧸ D) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    refine ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective D q
    show (2 : ℤ) • (Submodule.Quotient.mk x : N ⧸ D) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  haveI := Fintype.ofFinite (N ⧸ D)
  refine ⟨(Finset.univ : Finset (N ⧸ D)).image fun q => ((Quotient.out q : N) : M), ?_, ?_⟩
  · intro v hv
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hv
    exact (Quotient.out q).2
  · intro h hh
    let q : N ⧸ D := Submodule.Quotient.mk ⟨h, hh⟩
    have hq : Submodule.Quotient.mk (Quotient.out q) = q := Quotient.out_eq q
    rw [Submodule.Quotient.eq] at hq
    obtain ⟨w, hw⟩ := hq
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), -(w : M), N.neg_mem w.2, ?_⟩
    have := congrArg (fun z : N => (z : M)) hw
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, Submodule.coe_sub] at this
    have h2 : (2 : ℕ) • (w : M) = (2 : ℤ) • (w : M) := by rw [two_smul, two_smul]
    rw [smul_neg, h2, this]
    abel

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_finset_fixedUnit_eq_mul_fixed_sq (K : Type) [Field K] [NumberField K]
    (τ : K ≃+* K) : ∃ V : Finset K, ∀ u ∈ _root_.GlobalTheory.UnitSq.fixedUnits K τ, ∃ v ∈ V, ∃ w : K,
      w ≠ 0 ∧ τ w = w ∧ ((u : 𝓞 K) : K) = v * w ^ 2 := by
  classical
  obtain ⟨V, -, hV⟩ := exists_finset_submodule_eq_add_two_smul (M := Additive (𝓞 K)ˣ)
    (AddSubgroup.toIntSubmodule (_root_.GlobalTheory.UnitSq.fixedUnits K τ).toAddSubgroup)
  refine ⟨V.image fun v => (((Additive.toMul v : (𝓞 K)ˣ) : 𝓞 K) : K), fun u hu => ?_⟩
  obtain ⟨v, hv, w, hw, huv⟩ := hV (Additive.ofMul u) hu
  refine ⟨_, Finset.mem_image_of_mem _ hv, (((Additive.toMul w : (𝓞 K)ˣ) : 𝓞 K) : K), ?_, hw, ?_⟩
  · simp
  · have h := congrArg Additive.toMul huv
    simp only [toMul_ofMul, toMul_add, toMul_nsmul] at h
    rw [h]
    push_cast
    ring

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_apply_involution_eq_ord_primeMap {K : Type} [Field K] [NumberField K] (τ : K ≃+* K)
    (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 K)) (x : K) :
    _root_.GlobalTheory.FixNormCls.ord P (τ x) =
      _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) x := by
  have h := _root_.GlobalTheory.FixNormCls.ord_primeMap τ
    (_root_.GlobalTheory.FixNormCls.primeMap τ P) x
  rwa [_root_.GlobalTheory.FixNormCls.primeMap_primeMap τ hτ] at h

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_nat_prime_mem_heightOneSpectrum (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ P.asIdeal := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ P.asIdeal)
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite (𝓞 K ⧸ P.asIdeal) p
  haveI : NeZero p := ⟨hp0⟩
  refine ⟨p, (CharP.char_is_prime_of_pos (𝓞 K ⧸ P.asIdeal) p).out, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_eq_zero_of_not_mem_of_ne_zero {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) (h0 : z ≠ 0) (hz : z ∉ P.asIdeal) :
    _root_.GlobalTheory.FixNormCls.ord P (z : K) = 0 := by
  classical
  unfold _root_.GlobalTheory.FixNormCls.ord
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  have hI : ((Ideal.span {z} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact h0
  rw [FractionalIdeal.count_well_defined K P hI (a := 1) (J := Ideal.span {z}) (by simp),
    Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero P.associates_irreducible]
  rw [Nat.cast_zero, sub_zero, Nat.cast_eq_zero]
  by_contra hc
  have hspan : Ideal.span {z} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact h0
  have := (Associates.count_ne_zero_iff_dvd hspan P.irreducible).1 hc
  exact hz (Ideal.span_singleton_le_iff_mem _ |>.1 (Ideal.le_of_dvd this))

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem natCast_not_mem_of_prime_mem_not_dvd {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {ℓ d : ℕ} (hℓ : ℓ.Prime) (hP : (ℓ : 𝓞 K) ∈ P.asIdeal)
    (hd : ¬ ℓ ∣ d) : (d : 𝓞 K) ∉ P.asIdeal := by
  intro hdP
  have hcop : IsCoprime (ℓ : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : 𝓞 K) * (ℓ : 𝓞 K) + (v : 𝓞 K) * (d : 𝓞 K)) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : 𝓞 K)) huv
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hP) (P.asIdeal.mul_mem_left _ hdP)

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_nonneg_of_isIntegral' {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {z : K} (hz : IsIntegral ℤ z) :
    0 ≤ _root_.GlobalTheory.FixNormCls.ord P z := by
  obtain ⟨w, rfl⟩ : ∃ w : 𝓞 K, (w : K) = z := ⟨⟨z, hz⟩, rfl⟩
  unfold _root_.GlobalTheory.FixNormCls.ord
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K P _

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_eq_ord_add_ord_primeMap_of_isIntegral_mul {K : Type} [Field K] [NumberField K] (τ : K ≃+* K)
    (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 K)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 K) ∈ P.asIdeal) {a b x y : K} (ha0 : a ≠ 0) (hb : b ≠ 0)
    (hax : a = x * (b * τ b)) (hby : b * τ b = y * a) {d : ℕ} (hd : ¬ ℓ ∣ d)
    (hdx : IsIntegral ℤ ((d : K) * x)) (hdy : IsIntegral ℤ ((d : K) * y)) :
    _root_.GlobalTheory.FixNormCls.ord P a = _root_.GlobalTheory.FixNormCls.ord P b +
      _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) b := by
  have hτb : τ b ≠ 0 := by simpa using hb
  have hN : b * τ b ≠ 0 := mul_ne_zero hb hτb
  have hx0 : x ≠ 0 := by rintro rfl; simp at hax; exact ha0 hax
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_mul] at hby; exact hN hby
  have hxy : x * y = 1 := by
    exact mul_right_cancel₀ ha0 (by rw [one_mul, mul_assoc, ← hby, ← hax])
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero ℓ)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hord_d : _root_.GlobalTheory.FixNormCls.ord P (d : K) = 0 := by
    have h := ord_eq_zero_of_not_mem_of_ne_zero P (d : 𝓞 K) (by exact_mod_cast hd0)
      (natCast_not_mem_of_prime_mem_not_dvd P hℓ hP hd)
    simpa using h
  have h1 := ord_nonneg_of_isIntegral' P hdx
  have h2 := ord_nonneg_of_isIntegral' P hdy
  rw [_root_.GlobalTheory.FixNormCls.ord_mul P hdK hx0, hord_d] at h1
  rw [_root_.GlobalTheory.FixNormCls.ord_mul P hdK hy0, hord_d] at h2
  have h3 : _root_.GlobalTheory.FixNormCls.ord P x + _root_.GlobalTheory.FixNormCls.ord P y = 0 := by
    rw [← _root_.GlobalTheory.FixNormCls.ord_mul P hx0 hy0, hxy, _root_.GlobalTheory.FixNormCls.ord_one]
  rw [hax, _root_.GlobalTheory.FixNormCls.ord_mul P hx0 hN, _root_.GlobalTheory.FixNormCls.ord_mul P hb hτb,
    ord_apply_involution_eq_ord_primeMap τ hτ]
  omega

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_unit_eq_of_forall_ord_eq_zero {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.FixNormCls.ord P x = 0) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = x := by
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI
  have h' : ∀ P : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 := h
  simp only [h', zpow_zero, finprod_one] at key
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton] at key
  obtain ⟨z, hz⟩ := key
  exact ⟨z, by simpa [Units.smul_def, Algebra.smul_def] using hz⟩

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in

theorem _root_.GlobalTheory.FixNormField.fixed_classes_mod_norms : ∀ (K : Type) [Field K] [NumberField K]
    (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e := by
  intro K _ _ τ hτ S
  classical
  have hσσ := _root_.GlobalTheory.FixNormCls.primeMap_primeMap τ hτ
  letI : LinearOrder (HeightOneSpectrum (𝓞 K)) := IsWellOrder.linearOrder WellOrderingRel
  have hTfin := finite_heightOneSpectrum_containing_finset_nat K S
  set T := hTfin.toFinset with hT
  have hrep : ∀ c : ClassGroup (𝓞 K), ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c :=
    fun c => ClassGroup.induction K (fun I => ⟨I, rfl⟩) c
  choose rep hrep using hrep
  let prof : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → HeightOneSpectrum (𝓞 K) → ℤ :=
    fun κ P => (if P ∈ κ.2 then 1 else 0) +
      FractionalIdeal.count K P (rep κ.1 : FractionalIdeal (𝓞 K)⁰ K) +
      FractionalIdeal.count K (_root_.GlobalTheory.FixNormCls.primeMap τ P) (rep κ.1 : FractionalIdeal (𝓞 K)⁰ K)
  let good : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → K → Prop :=
    fun κ c => c ≠ 0 ∧ τ c = c ∧ ∀ P, _root_.GlobalTheory.FixNormCls.ord P c = prof κ P
  let rep2 : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → K :=
    fun κ => if h : ∃ c, good κ c then h.choose else 1
  have hrep2 : ∀ κ c, good κ c → good κ (rep2 κ) := fun κ c hc => by
    have h : ∃ c, good κ c := ⟨c, hc⟩
    dsimp only [rep2]
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨V, hV⟩ := exists_finset_fixedUnit_eq_mul_fixed_sq K τ
  refine ⟨(((Finset.univ ×ˢ T.powerset).image rep2) ×ˢ V).image (fun p => p.1 * p.2), ?_⟩
  intro a ha0 hτa hloc
  have hσa : ∀ P, _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) a =
      _root_.GlobalTheory.FixNormCls.ord P a := by
    intro P; rw [← ord_apply_involution_eq_ord_primeMap τ hτ, hτa]
  have hsplit : ∀ P, P ∉ T → _root_.GlobalTheory.FixNormCls.primeMap τ P = P →
      _root_.GlobalTheory.FixNormCls.ord P a % 2 = 0 := by
    intro P hP hfix
    obtain ⟨ℓ, hℓ, hℓP⟩ := exists_nat_prime_mem_heightOneSpectrum K P
    have hℓS : ℓ ∉ S := fun hS => hP (by
      rw [hT, Set.Finite.mem_toFinset]; exact ⟨ℓ, hS, hℓ.ne_zero, hℓP⟩)
    obtain ⟨b, x, y, hb, hax, hby, d, hd, hdx, hdy⟩ := hloc ℓ hℓ hℓS
    rw [ord_eq_ord_add_ord_primeMap_of_isIntegral_mul τ hτ P hℓ hℓP ha0 hb hax hby hd hdx hdy, hfix]
    omega
  let k : HeightOneSpectrum (𝓞 K) → ℤ := fun P =>
    if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a / 2
    else if P < _root_.GlobalTheory.FixNormCls.primeMap τ P then _root_.GlobalTheory.FixNormCls.ord P a else 0
  have hk : ∀ P, k P + k (_root_.GlobalTheory.FixNormCls.primeMap τ P) = _root_.GlobalTheory.FixNormCls.ord P a -
      (if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a % 2 else 0) := by
    intro P
    by_cases hfix : _root_.GlobalTheory.FixNormCls.primeMap τ P = P
    · simp only [k, hfix, if_true]; omega
    · have e1 : k P = if P < _root_.GlobalTheory.FixNormCls.primeMap τ P then
          _root_.GlobalTheory.FixNormCls.ord P a else 0 := by
        simp only [k]; rw [if_neg hfix]
      have e2 : k (_root_.GlobalTheory.FixNormCls.primeMap τ P) = if _root_.GlobalTheory.FixNormCls.primeMap τ P < P then
          _root_.GlobalTheory.FixNormCls.ord P a else 0 := by
        simp only [k, hσσ, hσa]; rw [if_neg fun h => hfix h.symm]
      rw [e1, e2, if_neg hfix, sub_zero]
      rcases lt_trichotomy P (_root_.GlobalTheory.FixNormCls.primeMap τ P) with h | h | h
      · rw [if_pos h, if_neg (lt_asymm h), add_zero]
      · exact absurd h.symm hfix
      · rw [if_neg (lt_asymm h), if_pos h, zero_add]
  have hkfin : ∀ᶠ P in Filter.cofinite, k P = 0 := by
    filter_upwards [FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ a)] with P hP
    have hP' : _root_.GlobalTheory.FixNormCls.ord P a = 0 := hP
    simp [k, hP']
  set J : FractionalIdeal (𝓞 K)⁰ K :=
    ∏ᶠ P : HeightOneSpectrum (𝓞 K), (P.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k P with hJ
  have hJ0 : J ≠ 0 := finprod_ne_zero fun P => zpow_ne_zero _ (by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.ne_bot)
  have hJcount : ∀ P, FractionalIdeal.count K P J = k P := fun P =>
    FractionalIdeal.count_finprod K P k hkfin
  set c0 := ClassGroup.mk K (Units.mk0 J hJ0) with hc0def
  set I := rep c0 with hIdef
  have hprin : ClassGroup.mk K (Units.mk0 J hJ0 * I⁻¹) = 1 := by
    rw [map_mul, map_inv, hIdef, hrep c0, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hprin
  obtain ⟨e, he⟩ := hprin
  have hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := I.ne_zero
  have he' : FractionalIdeal.spanSingleton (𝓞 K)⁰ e = J * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← he]; simp
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at he'
    exact mul_ne_zero hJ0 (inv_ne_zero hI0) he'.symm
  have heord : ∀ P, _root_.GlobalTheory.FixNormCls.ord P e =
      k P - FractionalIdeal.count K P (I : FractionalIdeal (𝓞 K)⁰ K) := by
    intro P
    show FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ e) = _
    rw [he', FractionalIdeal.count_mul K P hJ0 (inv_ne_zero hI0), FractionalIdeal.count_inv,
      hJcount]
    ring
  have hτe0 : τ e ≠ 0 := by simpa using he0
  set c := a / (e * τ e) with hc
  have hc0 : c ≠ 0 := div_ne_zero ha0 (mul_ne_zero he0 hτe0)
  have hτc : τ c = c := by rw [hc, map_div₀, map_mul, hτ, hτa, mul_comm (τ e)]
  set Rset := T.filter (fun P => _root_.GlobalTheory.FixNormCls.primeMap τ P = P ∧
    _root_.GlobalTheory.FixNormCls.ord P a % 2 = 1) with hRset
  have hgood : good (c0, Rset) c := by
    refine ⟨hc0, hτc, fun P => ?_⟩
    have hr : (if P ∈ Rset then (1 : ℤ) else 0) =
        (if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a % 2 else 0) := by
      by_cases hfix : _root_.GlobalTheory.FixNormCls.primeMap τ P = P
      · rw [if_pos hfix]
        by_cases hPT : P ∈ T
        · have h2 := Int.emod_two_eq_zero_or_one (_root_.GlobalTheory.FixNormCls.ord P a)
          rcases h2 with h2 | h2
          · rw [if_neg (by simp [hRset, h2]), h2]
          · rw [if_pos (by simp [hRset, hPT, hfix, h2]), h2]
        · rw [if_neg (by simp [hRset, hPT]), hsplit P hPT hfix]
      · rw [if_neg hfix, if_neg (by simp [hRset, hfix])]
    have h1 := hk P
    show _root_.GlobalTheory.FixNormCls.ord P c = (if P ∈ Rset then 1 else 0) +
      FractionalIdeal.count K P (I : FractionalIdeal (𝓞 K)⁰ K) +
      FractionalIdeal.count K (_root_.GlobalTheory.FixNormCls.primeMap τ P) (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [hc, _root_.GlobalTheory.FixNormCls.ord_div P ha0 (mul_ne_zero he0 hτe0),
      _root_.GlobalTheory.FixNormCls.ord_mul P he0 hτe0, ord_apply_involution_eq_ord_primeMap τ hτ, heord, heord, hr]
    linarith
  obtain ⟨hc10, hτc1, hc1ord⟩ := hrep2 _ _ hgood
  set c1 := rep2 (c0, Rset) with hc1def
  have hq : ∀ P, _root_.GlobalTheory.FixNormCls.ord P (c / c1) = 0 := by
    intro P
    rw [_root_.GlobalTheory.FixNormCls.ord_div P hc0 hc10, hgood.2.2 P, hc1ord P, sub_self]
  obtain ⟨u, hu⟩ := exists_unit_eq_of_forall_ord_eq_zero (div_ne_zero hc0 hc10) hq
  have hufix : u ∈ _root_.GlobalTheory.UnitSq.fixedUnits K τ := by
    show τ ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K)
    rw [hu, map_div₀, hτc, hτc1]
  obtain ⟨v, hvV, w, hw0, hτw, huvw⟩ := hV u hufix
  refine ⟨c1 * v, Finset.mem_image.2 ⟨(c1, v), Finset.mem_product.2
    ⟨Finset.mem_image.2 ⟨(c0, Rset), Finset.mem_product.2 ⟨Finset.mem_univ _,
      Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩, rfl⟩, hvV⟩, rfl⟩,
    e * w, mul_ne_zero he0 hw0, ?_⟩
  rw [hu] at huvw
  have hcv : c = c1 * (v * w ^ 2) := by rw [← huvw]; field_simp
  have hac : a = c * (e * τ e) := by rw [hc]; field_simp
  rw [hac, hcv, map_mul, hτw]
  ring

end GlobalTheory.FixNormField
