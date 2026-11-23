import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSign

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem geom_sin (k : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) (w : ℂ) (hw : w = Complex.exp (θ * Complex.I) ^ 2) :
    (w ^ k)⁻¹ * ∑ j ∈ Finset.range (2 * k + 1), w ^ j =
      ((Real.sin ((2 * k + 1 : ℕ) * θ) / Real.sin θ : ℝ) : ℂ) := by
  have hs : ((Real.sin θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h
  obtain ⟨e, he⟩ : ∃ e, e = Complex.exp (θ * Complex.I) := ⟨_, rfl⟩
  have he0 : e ≠ 0 := he ▸ Complex.exp_ne_zero _
  have h1 : ((Real.sin θ : ℝ) : ℂ) = (e⁻¹ - e) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul, Complex.exp_neg, he]
  have h2 : ((Real.sin ((2 * k + 1 : ℕ) * θ) : ℝ) : ℂ) = ((e ^ (2 * k + 1))⁻¹ - e ^ (2 * k + 1)) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, neg_mul, Complex.exp_neg, he, ← Complex.exp_nat_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  have h3 := geom_sum_mul w (2 * k + 1)
  rw [← he] at hw
  subst hw
  rw [Complex.ofReal_div, eq_div_iff hs, h1, h2]
  generalize ∑ j ∈ Finset.range (2 * k + 1), (e ^ 2) ^ j = S at h3 ⊢
  have h4 : (e ^ 2) ^ k = e ^ (2 * k) := by rw [← pow_mul]
  have h5 : (e ^ 2) ^ (2 * k + 1) = e ^ (2 * k) * e ^ (2 * k) * e ^ 2 := by ring
  rw [h5] at h3
  rw [h4, pow_succ]
  have h6 : e ^ (2 * k) ≠ 0 := pow_ne_zero _ he0
  generalize e ^ (2 * k) = a at h3 h6 ⊢
  field_simp
  linear_combination (-1 : ℂ) * h3

private theorem exists_zeta (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]
    (φ : L →+* ℂ) : ∃ ζ : L, IsPrimitiveRoot ζ M ∧ φ ζ = Complex.exp (2 * Real.pi * Complex.I / M) := by
  have h0 := (IsCyclotomicExtension.zeta_spec M ℚ L).map_of_injective φ.injective
  have h1 := Complex.isPrimitiveRoot_exp M (NeZero.ne M)
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have h2 : φ (IsCyclotomicExtension.zeta M ℚ L ^ i) = Complex.exp (2 * Real.pi * Complex.I / M) := by
    rw [map_pow, hi]
  exact ⟨_, IsPrimitiveRoot.of_map_of_injective (h2 ▸ h1) φ.injective, h2⟩

private theorem sin_ne (M a : ℕ) (hM : 2 < M) (h : a.Coprime M) : Real.sin (Real.pi * ((a : ℝ) / M)) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h0
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) * M = a := by
    have := Real.pi_pos
    field_simp at hn
    linarith
  have h2 : n * (M : ℤ) = a := by exact_mod_cast h1
  have h3 : M ∣ a := Int.natCast_dvd_natCast.1 ⟨n, by rw [← h2, mul_comm]⟩
  have := Nat.Coprime.eq_one_of_dvd h.symm h3
  omega

theorem UpperTheory.V.FW.sgnUnit :
    ∀ (M c : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L], c.Coprime M → Odd c → 2 < M → ∃ φ : L →+* ℂ, (fun t : (ZMod M)ˣ => ((c * (t : ZMod M).val / M : ℕ) : ZMod 2)) ∈ sgnE (embT M L φ) := by
  intro M c _ L _ _ _ _ hc hodd hM
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨ζ, hζ, hφ⟩ := exists_zeta M L φ
  refine ⟨φ, AddSubgroup.subset_closure ?_⟩
  have hz := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit (hζ.toInteger ^ (k * (M - 1)) * ∑ j ∈ Finset.range (2 * k + 1), hζ.toInteger ^ j) :=
    ((hz.isUnit (by omega)).pow _).mul (hz.geom_sum_isUnit (by omega) hc)
  have hinv : ζ ^ (k * (M - 1)) = (ζ ^ k)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega), mul_comm, pow_mul,
      hζ.pow_eq_one, one_pow]
  have hval : ((hu.unit : 𝓞 L) : L) = (ζ ^ k)⁻¹ * ∑ j ∈ Finset.range (2 * k + 1), ζ ^ j := by
    rw [IsUnit.unit_spec, ← hinv]
    change algebraMap (𝓞 L) L _ = _
    simp only [map_mul, map_pow, map_sum]
    rfl
  have hM0 : (0 : ℝ) < M := by positivity
  have key : ∀ a : ℕ, a.Coprime M → ∀ ψ : L →+* ℂ, ψ ζ = φ ζ ^ a → ψ ((hu.unit : 𝓞 L) : L) =
      ((Real.sin ((2 * k + 1 : ℕ) * (Real.pi * ((a : ℝ) / M))) / Real.sin (Real.pi * ((a : ℝ) / M)) : ℝ) : ℂ) := by
    intro a ha ψ hψ
    rw [hval, ← geom_sin k _ (sin_ne M a hM ha) (ψ ζ)]
    · simp only [map_mul, map_pow, map_sum, map_inv₀]
    · rw [hψ, hφ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  refine ⟨hu.unit, ?_, ?_⟩
  · apply φ.injective
    have h2 : φ (cE L ((hu.unit : 𝓞 L) : L)) = starRingEnd ℂ (φ ((hu.unit : 𝓞 L) : L)) :=
      IsCMField.complexEmbedding_complexConj L φ _
    rw [h2, key 1 (Nat.coprime_one_left M) φ (pow_one _).symm, Complex.conj_ofReal]
  · funext t
    have ht := ZMod.val_coe_unit_coprime t
    have htl := ZMod.val_lt (t : ZMod M)
    have h1 : embT M L φ t ζ = φ ζ ^ (t : ZMod M).val := by
      change φ (sg M L t ζ) = _
      rw [sg_apply M L t hζ.pow_eq_one, map_pow]
    simp only [sgn]
    rw [key _ ht _ h1, Complex.ofReal_re]
    generalize (t : ZMod M).val = a at ht htl
    have hlt : (a : ℝ) / M < 1 := (div_lt_one hM0).2 (by exact_mod_cast htl)
    have hpos : 0 < Real.sin (Real.pi * ((a : ℝ) / M)) := by
      refine lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_) (sin_ne M a hM ht).symm
      have := Real.pi_pos
      nlinarith
    have he : ((2 * k + 1 : ℕ) : ℝ) * (Real.pi * ((a : ℝ) / M)) = Real.pi * ((((2 * k + 1) * a : ℕ) : ℝ) / M) := by
      push_cast
      ring
    have hs := sinSign ((((2 * k + 1) * a : ℕ) : ℝ) / M) (by positivity) (sin_ne M _ hM (Nat.Coprime.mul_left hc ht))
    rw [Nat.floor_div_eq_div] at hs
    rw [he]
    simp only [div_lt_iff₀ hpos, zero_mul, hs]
    split_ifs with h
    · exact h.natCast_zmod_two
    · exact (Nat.not_odd_iff_even.1 h).natCast_zmod_two
