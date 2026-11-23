import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RationalLocal
import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.IdeleGroups.Rational

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

namespace RationalSymbol

attribute [local instance] galCommGroup

section Infinite

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

theorem conjAt_apply_of_pow_eq_one (w : InfinitePlace L) {ζ : L} {n : ℕ} (hn : n ≠ 0)
    (hζ : ζ ^ n = 1) : conjAt ℚ w ζ = ζ⁻¹ := by
  have hc : ComplexEmbedding.IsConj w.embedding (conjAt ℚ w) := by
    by_cases hw : w.IsReal
    · rw [conjAt_of_isReal hw]
      exact ComplexEmbedding.isConj_one_iff.2 (InfinitePlace.isReal_iff.1 hw)
    · exact isConj_conjAt (InfinitePlace.isRamified_iff.2
        ⟨InfinitePlace.not_isReal_iff_isComplex.1 hw, RationalIdeles.isReal_infinitePlace _⟩)
  apply w.embedding.injective
  rw [hc.eq, map_inv₀, ← starRingEnd_apply, ← Complex.inv_eq_conj]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hn

variable (L) [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem infiniteLocalSymbol_apply_of_pow_eq_one (w : InfinitePlace ℚ) (x : w.Completionˣ) {ζ : L}
    {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    infiniteLocalSymbol L w x ζ =
      if InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (RationalIdeles.isReal_infinitePlace w) x < 0 then ζ⁻¹ else ζ := by
  obtain ⟨w'⟩ := IdeleNorm.nonempty_infinitePlacesOver L w
  rw [infiniteLocalSymbol_apply L w (RationalIdeles.isReal_infinitePlace w) w' x]
  split_ifs
  · exact conjAt_apply_of_pow_eq_one _ hn hζ
  · rfl

theorem extensionEmbeddingOfIsReal_infiniteProj (w : InfinitePlace ℚ) (y : IdeleGroup ℚ) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (RationalIdeles.isReal_infinitePlace w)
      (infiniteProj w y : w.Completion) = (RationalIdeles.realPart y : ℝ) := by
  obtain rfl : w = default := Subsingleton.elim _ _
  rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply]
  rfl

end Infinite

theorem exists_finprod_eq_prod_mul {ι G : Type*} [CommGroup G] (H : Subgroup G) {f : ι → G}
    (hf : (Function.mulSupport f).Finite) (T : Finset ι) (hT : ∀ i ∉ T, f i ∈ H) :
    ∃ h ∈ H, ∏ᶠ i, f i = (∏ i ∈ T, f i) * h := by
  refine ⟨∏ᶠ i ∈ Set.univ \ (T : Set ι), f i, finprod_mem_induction (· ∈ H) H.one_mem
    (fun _ _ ↦ H.mul_mem) (fun i hi ↦ hT i hi.2), ?_⟩
  rw [← finprod_mem_coe_finset, finprod_mem_mul_sdiff' (Set.subset_univ _) (by simpa using hf),
    finprod_mem_univ]

section Symbol

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_apply_eq_of_forall_notMem (y : IdeleGroup ℚ) (ζ : L)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v ∉ T, localSymbol L v (finiteProj v y) ζ = ζ) :
    ideleSymbol ℚ L y ζ = (∏ v ∈ T, localSymbol L v (finiteProj v y))
      (infiniteLocalSymbol L default (infiniteProj default y) ζ) := by
  obtain ⟨h, hh, heq⟩ := exists_finprod_eq_prod_mul (MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ)
    (hasFiniteMulSupport_localSymbol L y) T fun v hv ↦ by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hT v hv
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hh
  rw [ideleSymbol_apply, heq, Fintype.prod_subsingleton _ default, mul_right_comm,
    AlgEquiv.mul_apply, hh, AlgEquiv.mul_apply]

end Symbol

section Generators

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem padicRingEquiv_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℚˣ) :
    padicRingEquiv v (finiteProj v (diagonal ℚ a) : v.adicCompletion ℚ) = ((a : ℚ) : ℚ_[prime v]) := by
  let f : ℚ →+* ℚ_[prime v] := (padicRingEquiv v).toRingHom.comp
    (@algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v))
  exact eq_ratCast f (a : ℚ)

theorem prime_injective : Function.Injective prime := fun _ _ h ↦
  Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

theorem coprime_prime {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') :
    (prime v).Coprime (prime v') :=
  (Nat.coprime_primes Fact.out Fact.out).2 fun e ↦ h (prime_injective e)

def primeUnit {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') : ℤ_[prime v]ˣ :=
  (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 (coprime_prime h))).unit

theorem coe_primeUnit {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') :
    ((primeUnit h : ℤ_[prime v]ˣ) : ℤ_[prime v]) = (prime v' : ℤ_[prime v]) := by
  simp [primeUnit]

def primeRat (v : HeightOneSpectrum (𝓞 ℚ)) : ℚˣ :=
  Units.mk0 (prime v : ℚ) (Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero)

def placeOf (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm p

theorem prime_placeOf (p : Nat.Primes) : prime (placeOf p) = p :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

@[simp]
theorem coe_primeRat (v : HeightOneSpectrum (𝓞 ℚ)) : ((primeRat v : ℚˣ) : ℚ) = (prime v : ℚ) :=
  rfl

variable {L}

theorem localSymbol_neg_one_of_ne {v v₀ : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v₀) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v (finiteProj v (diagonal ℚ (-1))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (-1) 0
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) (Nat.Coprime.pow_left n (coprime_prime hv.symm)) hζ,
    pow_zero, pow_one]

theorem localSymbol_neg_one_self (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (-1))) ζ = ζ⁻¹ := by
  rw [localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (-1) 0
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) hζ]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, LocalField.pow_eq_pow_of_natCast_eq hζ (b := 0) (by simp [ZMod.natCast_val]),
    pow_zero]

theorem localSymbol_prime_of_ne {v v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (hv₀ : v ≠ v₀) (hv' : v ≠ v')
    {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v (finiteProj v (diagonal ℚ (primeRat v'))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (primeUnit hv') 0
    (by rw [padicRingEquiv_finiteProj_diagonal, coe_primeUnit]; simp)
    (Nat.Coprime.pow_left n (coprime_prime hv₀.symm)) hζ, pow_zero, pow_one]

theorem localSymbol_prime_self (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (primeRat v₀))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ 1 1
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) hζ]
  conv_rhs => rw [← pow_one ζ]
  exact LocalField.pow_eq_pow_of_natCast_eq hζ (by simp [ZMod.natCast_val])

theorem localSymbol_prime_at_other {v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (h : v₀ ≠ v') {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (primeRat v'))) ζ =
      ζ ^ (PadicInt.toZModPow n (((primeUnit h)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val :=
  localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (primeUnit h) 0
    (by rw [padicRingEquiv_finiteProj_diagonal, coe_primeUnit]; simp) hζ

theorem localSymbol_prime_at_self {v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (h : v₀ ≠ v') {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v' (finiteProj v' (diagonal ℚ (primeRat v'))) ζ = ζ ^ prime v' := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v' L _ 1 1
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp)
    (Nat.Coprime.pow_left n (coprime_prime h)) hζ, pow_one]

variable (L)

theorem ideleSymbol_diagonal_neg_one (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) : ideleSymbol ℚ L (diagonal ℚ (-1)) ζ = ζ := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀}
      (fun v hv ↦ localSymbol_neg_one_of_ne (by simpa using hv) hζ),
    Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,
    extensionEmbeddingOfIsReal_infiniteProj, if_pos (by rw [RationalIdeles.realPart_diagonal]; simp),
    map_inv₀, localSymbol_neg_one_self v₀ hζ, inv_inv]

theorem ideleSymbol_diagonal_prime (v₀ v' : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) : ideleSymbol ℚ L (diagonal ℚ (primeRat v')) ζ = ζ := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  have hinf : infiniteLocalSymbol L default (infiniteProj default (diagonal ℚ (primeRat v'))) ζ =
      ζ := by
    rw [infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ, extensionEmbeddingOfIsReal_infiniteProj,
      if_neg (by rw [RationalIdeles.realPart_diagonal]; simp)]
  by_cases h : v₀ = v'
  · subst h
    rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀}
        (fun v hv ↦ localSymbol_prime_of_ne (by simpa using hv) (by simpa using hv) hζ),
      Finset.prod_singleton, hinf, localSymbol_prime_self v₀ hζ]
  · classical
    have : NeZero (prime v₀ ^ n) := ⟨hn⟩
    rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀, v'}
        (fun v hv ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
          exact localSymbol_prime_of_ne hv.1 hv.2 hζ),
      Finset.prod_pair h, hinf, AlgEquiv.mul_apply, localSymbol_prime_at_self h hζ, map_pow,
      localSymbol_prime_at_other h hζ, ← pow_mul]
    conv_rhs => rw [← pow_one ζ]
    refine LocalField.pow_eq_pow_of_natCast_eq hζ ?_
    have hu : ((prime v' : ℕ) : ℤ_[prime v₀]) = ((primeUnit h : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀]) :=
      (coe_primeUnit h).symm
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← map_natCast (PadicInt.toZModPow (p := prime v₀) n),
      hu, ← map_mul, Units.inv_mul, map_one, Nat.cast_one]

end Generators

theorem mem_of_neg_one_mem_of_primeRat_mem (H : Subgroup ℚˣ) (hneg : -1 ∈ H)
    (hp : ∀ v, primeRat v ∈ H) (a : ℚˣ) : a ∈ H := by
  have hnat : ∀ n : ℕ, ∀ h : (n : ℚ) ≠ 0, Units.mk0 (n : ℚ) h ∈ H := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd Nat.cast_zero h
    | one =>
      intro h
      convert H.one_mem
      ext
      simp
    | prime p hp' =>
      intro h
      convert hp (placeOf ⟨p, hp'⟩) using 1
      ext
      rw [Units.val_mk0, coe_primeRat, prime_placeOf ⟨p, hp'⟩]
    | mul a b ha hb =>
      intro h
      have ha0 : (a : ℚ) ≠ 0 := fun h0 ↦ h (by rw [Nat.cast_mul, h0, zero_mul])
      have hb0 : (b : ℚ) ≠ 0 := fun h0 ↦ h (by rw [Nat.cast_mul, h0, mul_zero])
      convert H.mul_mem (ha ha0) (hb hb0) using 1
      ext
      simp
  have hint : ∀ z : ℤ, ∀ h : (z : ℚ) ≠ 0, Units.mk0 (z : ℚ) h ∈ H := by
    intro z h
    have h' : ((z.natAbs : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 (Int.cast_ne_zero.1 h))
    rcases Int.natAbs_eq z with hz | hz
    · convert hnat _ h' using 1
      ext
      rw [Units.val_mk0, Units.val_mk0, ← Int.cast_natCast, ← hz]
    · convert H.mul_mem hneg (hnat _ h') using 1
      ext
      rw [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, Units.val_mk0, neg_one_mul,
        ← Int.cast_natCast, ← Int.cast_neg, ← hz]
  have h1 := hint a.1.num (Int.cast_ne_zero.2 (Rat.num_ne_zero.2 a.ne_zero))
  have h2 := hint (a.1.den : ℤ) (by exact_mod_cast a.1.den_nz)
  convert H.mul_mem h1 (H.inv_mem h2) using 1
  ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, Int.cast_natCast,
    ← div_eq_mul_inv, Rat.num_div_den]

theorem apply_eq_of_pow_eq_one_of_forall_prime_pow {L : Type*} [Field L] [CharZero L] (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ p k : ℕ, p.Prime → ∀ ζ : L, ζ ^ (p ^ k) = 1 → σ ζ = ζ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  induction n using Nat.recOnPosPrimePosCoprime generalizing ζ with
  | prime_pow p k hp _ => exact hσ p k hp ζ hζ
  | zero => exact absurd rfl hn
  | one => rw [pow_one] at hζ; rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hζ
      exact zero_ne_one hζ
    have hA : σ (ζ ^ a) = ζ ^ a :=
      ihb (by omega) (by rw [← pow_mul, hζ])
    have hB : σ (ζ ^ b) = ζ ^ b :=
      iha (by omega) (by rw [← pow_mul, mul_comm b a, hζ])
    have e : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one, Nat.cast_one]
    have hz : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← e,
        zpow_one]
    rw [hz, map_mul, map_zpow₀, map_zpow₀, hA, hB]

section Main

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_diagonal_apply_of_pow_eq_one_of_prime_pow (a : ℚˣ)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    ideleSymbol ℚ L (diagonal ℚ a) ζ = ζ := by
  let H : Subgroup ℚˣ :=
    (MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ).comap ((ideleSymbol ℚ L).comp (diagonal ℚ))
  have key : ∀ b, b ∈ H ↔ ideleSymbol ℚ L (diagonal ℚ b) ζ = ζ := fun b ↦ by
    simp only [H, Subgroup.mem_comap, MonoidHom.comp_apply, MulAction.mem_stabilizer_iff,
      AlgEquiv.smul_def]
  exact (key a).1 (mem_of_neg_one_mem_of_primeRat_mem H
    ((key _).2 (ideleSymbol_diagonal_neg_one L v₀ hζ))
    (fun v' ↦ (key _).2 (ideleSymbol_diagonal_prime L v₀ v' hζ)) a)

theorem ideleSymbol_diagonal_apply_of_pow_eq_one (a : ℚˣ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : ideleSymbol ℚ L (diagonal ℚ a) ζ = ζ :=
  apply_eq_of_pow_eq_one_of_forall_prime_pow _ (fun p k hp ξ hξ ↦ by
    exact ideleSymbol_diagonal_apply_of_pow_eq_one_of_prime_pow L a (placeOf ⟨p, hp⟩) (n := k)
      (by rw [prime_placeOf ⟨p, hp⟩]; exact hξ)) hn hζ

theorem ideleSymbol_diagonal_eq_one (S : Set ℕ) [IsCyclotomicExtension S ℚ L] (a : ℚˣ) :
    ideleSymbol ℚ L (diagonal ℚ a) = 1 :=
  IsCyclotomicExtension.algEquiv_eq_of_apply_eq S ℚ L fun m hm hm0 ↦ by
    obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hm hm0
    exact ⟨r, hr, ideleSymbol_diagonal_apply_of_pow_eq_one L a hm0 hr.pow_eq_one⟩

end Main

end RationalSymbol

end

end GroundTheory.Global
