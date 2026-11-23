import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section aux

variable (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

private theorem xMul_conjI_eq (P : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K P t = P.map (sgO M K t).symm := (Ideal.map_symm (sgO M K t)).symm

private theorem xMul_conjI_mul (P Q : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K (P * Q) t = conjI M K P t * conjI M K Q t := by
  simp only [xMul_conjI_eq, Ideal.map_mul]

private theorem xMul_conjI_pow (P : Ideal (𝓞 K)) (n : ℕ) (t : (ZMod M)ˣ) :
    conjI M K (P ^ n) t = conjI M K P t ^ n := by
  simp only [xMul_conjI_eq, Ideal.map_pow]

private theorem xMul_conj (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = (starRingEnd ℂ) (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have h : φ.toRatAlgHom.comp (sg M K (-1) : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    have h1 : sg M K (-1) ζ * ζ = 1 := by
      rw [sg_apply M K _ hζ.pow_eq_one, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      simp
    have h2 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 (NeZero.ne M)
    have h4 : φ (sg M K (-1) ζ) * φ ζ = 1 := by rw [← map_mul, h1, map_one]
    change φ (sg M K (-1) ζ) = (starRingEnd ℂ) (φ ζ)
    rw [eq_inv_of_mul_eq_one_left h4, Complex.inv_eq_conj h3]
  exact DFunLike.congr_fun h x

private theorem xMul_root (ζ : K) (k : ℕ) (hk : k ≠ 0) (h : ζ ^ k = 1) : ζ * sg M K (-1) ζ = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply φ.injective
  have h2 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hk
  have h0 : φ ζ ≠ 0 := by
    intro h0
    simp [h0] at h3
  rw [map_mul, xMul_conj, map_one, ← Complex.inv_eq_conj h3, mul_inv_cancel₀ h0]

private noncomputable def xMul_sp : K →*₀ FractionalIdeal (𝓞 K)⁰ K where
  toFun x := FractionalIdeal.spanSingleton (𝓞 K)⁰ x
  map_zero' := FractionalIdeal.spanSingleton_zero
  map_one' := FractionalIdeal.spanSingleton_one
  map_mul' x y := (FractionalIdeal.spanSingleton_mul_spanSingleton x y).symm

private theorem xMul_sp_eq (x : K) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = xMul_sp K x := rfl

end aux

theorem UpperTheory.V.ML.xMul :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ),
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (X Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔟 Y → IsX M K b (𝔞 * 𝔟) (X * Y)) ∧
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (Z Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b (𝔞 * 𝔟) Z → IsX M K b 𝔟 Y → IsX M K b 𝔞 (Z / Y)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X : K) (n : ℕ), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b (𝔞 ^ n) (X ^ n)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X ζ : K) (k : ℕ), k ≠ 0 → ζ ^ k = 1 → IsX M K b 𝔞 X → IsX M K b 𝔞 (ζ * X)) ∧
    ∀ y : 𝓞 K, y ≠ 0 → IsX M K b (Ideal.span {y}) (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (y : K) ^ th M b t) := by
  intro M _ K _ _ _ b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro 𝔞 𝔟 X Y - - ⟨hX, hX'⟩ ⟨hY, hY'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, hY, one_mul]
    · rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hX', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 𝔟 Z Y - - ⟨hZ, hZ'⟩ ⟨hY, hY'⟩
    have hY0 : Y ≠ 0 := by
      rintro rfl
      simp at hY
    refine ⟨?_, ?_⟩
    · rw [map_div₀, div_mul_div_comm, hZ, hY, div_one]
    · have h0 : xMul_sp K Y ≠ 0 := (map_ne_zero _).2 hY0
      rw [xMul_sp_eq] at hZ' hY' ⊢
      rw [map_div₀, div_eq_iff h0, hZ', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 X n - ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_pow, ← mul_pow, hX, one_pow]
    · rw [xMul_sp_eq] at hX' ⊢
      rw [map_pow, hX', ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [xMul_conjI_pow, FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · rintro 𝔞 X ζ k hk hζ ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, xMul_root M K ζ k hk hζ, one_mul]
    · rw [← hX', eq_comm, FractionalIdeal.spanSingleton_eq_spanSingleton]
      have hi : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hζ ▸ isIntegral_one)
      obtain ⟨z, rfl⟩ : ∃ z : 𝓞 K, (z : K) = ζ := ⟨⟨ζ, hi⟩, rfl⟩
      have hu : IsUnit z := IsUnit.of_pow_eq_one (n := k) (Subtype.ext hζ) hk
      obtain ⟨u, rfl⟩ := hu
      refine ⟨u, ?_⟩
      rw [Units.smul_def, Algebra.smul_def]
  · intro y hy
    have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
    refine ⟨?_, ?_⟩
    · rw [map_prod, ← Equiv.prod_comp (Equiv.neg (ZMod M)ˣ) (fun t => sg M K (-1) ((sg M K t)⁻¹ (y : K) ^ th M b t)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t _ => ?_
      have h1 : sg M K (-1) ((sg M K (-t))⁻¹ (y : K)) = (sg M K t)⁻¹ (y : K) := by
        rw [← AlgEquiv.mul_apply, ← map_inv, ← map_inv, ← map_mul]
        congr 2
        simp [inv_neg]
      have h2 : (sg M K t)⁻¹ (y : K) ≠ 0 := (map_ne_zero _).2 hy'
      rw [Equiv.neg_apply, map_zpow₀, h1, Units.val_neg, th_neg, zpow_neg]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h2)
    · rw [xMul_sp_eq, map_prod]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [map_zpow₀, xMul_conjI_eq, Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton]
      rfl
