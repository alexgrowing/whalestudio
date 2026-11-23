import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Loc

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

theorem quo_mul' (a b : (Etau K τ)ˣ) : quo (a * b) = quo a * quo b := by
  simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring

theorem quo_one' : quo (1 : (Etau K τ)ˣ) = 1 := by simp [quo]

theorem algebraMap_etau (a : O) :
    algebraMap O (Etau K τ) a = algebraMap K (Etau K τ) (algebraMap O K a) :=
  IsScalarTower.algebraMap_apply O K _ a

theorem isIntegral_star {x : Etau K τ} (hx : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Etau K τ →ₐ[O] Etau K τ :=
    { starRingEnd (Etau K τ) with
      commutes' := fun r => by
        ext <;> simp [algebraMap_etau, starRingEnd_apply] }
  exact hx.map f

theorem isIntegral_of_trace_norm {x : Etau K τ} (t n : O) (ht : QuadraticAlgebra.trace x = algebraMap O K t)
    (hn : QuadraticAlgebra.norm x = algebraMap O K n) : IsIntegral O x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · have hz := QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero x
    rw [Algebra.smul_def, ht, hn, ← algebraMap_etau, ← algebraMap_etau] at hz
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [← hz]

end

section
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem two_ne_zero_of_isLoc (h : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have hu := h.two.map (algebraMap O K)
  rw [map_ofNat] at hu
  exact hu.ne_zero

theorem int_denom (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ x : Etau K τ, IsIntegral O x →
      ∃ a b : O, algebraMap O K c * x.re = algebraMap O K a ∧ algebraMap O K c * x.im = algebraMap O K b := by
  classical
  haveI := h.frac
  have inj : Function.Injective (algebraMap K (Etau K τ)) := fun r s hrs => by
    simpa using congrArg QuadraticAlgebra.re hrs
  have down : ∀ y : K, IsIntegral O (algebraMap K (Etau K τ) y) → ∃ a : O, algebraMap O K a = y := by
    intro y hy
    have hy' : IsIntegral O y :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Etau K τ)) inj).mp hy
    exact IsIntegrallyClosed.isIntegral_iff.mp hy'
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := O) τ
  obtain ⟨d1, d2, hd2, hd⟩ := IsFractionRing.div_surjective (A := O) (τ ^ 2 - 4)
  have hq0 : algebraMap O K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hd20 : algebraMap O K d2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd2
  have hd10 : algebraMap O K d1 ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hd
    exact hτ hd.symm
  have eτ : τ * algebraMap O K q = algebraMap O K p := by
    rw [← hpq, div_mul_cancel₀ _ hq0]
  have eD : (τ ^ 2 - 4) * algebraMap O K d2 = algebraMap O K d1 := by
    rw [← hd, div_mul_cancel₀ _ hd20]
  obtain ⟨u, hu⟩ := h.two.exists_right_inv
  have eu : algebraMap O K u * 2 = 1 := by
    have h2 := congrArg (algebraMap O K) hu
    rw [map_mul, map_one, map_ofNat] at h2
    rw [mul_comm]
    exact h2
  refine ⟨q * d1 * d2, ?_, ?_⟩
  · have hc : algebraMap O K (q * d1 * d2) ≠ 0 := by
      rw [map_mul, map_mul]
      exact mul_ne_zero (mul_ne_zero hq0 hd10) hd20
    intro h0
    apply hc
    rw [h0, map_zero]
  intro x hx
  obtain ⟨t, ht⟩ := down (QuadraticAlgebra.trace x) (by
    rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
    exact hx.add (isIntegral_star hx))
  obtain ⟨n, hn⟩ := down (QuadraticAlgebra.norm x) (by
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact hx.mul (isIntegral_star hx))
  rw [QuadraticAlgebra.trace_def] at ht
  rw [QuadraticAlgebra.norm_def] at hn
  have edisc : (τ ^ 2 - 4) * x.im ^ 2 = (algebraMap O K t) ^ 2 - 4 * algebraMap O K n := by
    rw [ht, hn]
    ring
  have hYint : IsIntegral O (algebraMap O K d1 * algebraMap O K d2 * x.im) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (d1 * d2 ^ 3 * (t ^ 2 - 4 * n)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      simp only [map_mul, map_pow, map_sub, map_ofNat]
      linear_combination (algebraMap O K d1 * algebraMap O K d2 ^ 3) * edisc -
        (algebraMap O K d1 * algebraMap O K d2 ^ 2 * x.im ^ 2) * eD
  obtain ⟨b0, hb0⟩ := IsIntegrallyClosed.isIntegral_iff.mp hYint
  refine ⟨u * (q * d1 * d2 * t - p * b0), q * b0, ?_, ?_⟩
  · simp only [map_mul, map_sub]
    rw [hb0]
    linear_combination (-(algebraMap O K q * algebraMap O K d1 * algebraMap O K d2 * x.re)) * eu -
      (algebraMap O K u * algebraMap O K q * algebraMap O K d1 * algebraMap O K d2) * ht -
      (algebraMap O K u * algebraMap O K d1 * algebraMap O K d2 * x.im) * eτ
  · simp only [map_mul]
    rw [hb0]
    ring

theorem finite_quot_span (h : IsLoc O Δ) {m : O} (hm : m ≠ 0) : Finite (O ⧸ Ideal.span {m}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {m} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
    have := h.fin
    rw [← hmax]
    exact this
  rw [hn, ← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow ⟨{ϖ}, by simp⟩ n

theorem cint_relIndex_ne_zero (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) {m : O} (hm : m ≠ 0)
    (H : Subgroup (Etau K τ)ˣ)
    (hH : ∀ z ∈ Cint O τ, ∀ r : Etau K τ, IsIntegral O r → quo z = 1 + algebraMap O K m • r → z ∈ H) :
    H.relIndex (Cint O τ) ≠ 0 := by
  classical
  haveI := h.frac
  obtain ⟨c, hc, hcx⟩ := int_denom h hτ
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := O) τ
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hQq : algebraMap O K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hQc : algebraMap O K c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  have eτ : τ * algebraMap O K q = algebraMap O K p := by
    rw [← hpq, div_mul_cancel₀ _ hQq]
  have hM0 : c * m * q ≠ 0 := mul_ne_zero (mul_ne_zero hc hm) hq0
  haveI : Finite (O ⧸ Ideal.span {c * m * q}) := finite_quot_span h hM0
  have hint : ∀ z : Cint O τ, IsIntegral O (quo z.1) ∧ IsIntegral O (quo z.1⁻¹) := fun z => z.2
  let A : Cint O τ → O := fun z => Classical.choose (hcx _ (hint z).1)
  let B : Cint O τ → O := fun z => Classical.choose (Classical.choose_spec (hcx _ (hint z).1))
  have hAB : ∀ z, algebraMap O K c * (quo z.1).re = algebraMap O K (A z) ∧
      algebraMap O K c * (quo z.1).im = algebraMap O K (B z) :=
    fun z => Classical.choose_spec (Classical.choose_spec (hcx _ (hint z).1))
  let f : Cint O τ → (O ⧸ Ideal.span {c * m * q}) × (O ⧸ Ideal.span {c * m * q}) :=
    fun z => (Ideal.Quotient.mk _ (A z), Ideal.Quotient.mk _ (B z))
  have key : ∀ z1 z2 : Cint O τ, f z1 = f z2 → z1⁻¹ * z2 ∈ H.subgroupOf (Cint O τ) := by
    intro z1 z2 hf
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hf.1.symm)
    obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hf.2.symm)
    have hr : IsIntegral O (⟨algebraMap O K q * algebraMap O K s, algebraMap O K q * algebraMap O K s'⟩ :
        Etau K τ) := by
      apply isIntegral_of_trace_norm (2 * q * s + p * s') (q * q * s * s + p * q * s * s' + q * q * s' * s')
      · rw [QuadraticAlgebra.trace_def]
        simp only [map_add, map_mul, map_ofNat]
        linear_combination (algebraMap O K s') * eτ
      · rw [QuadraticAlgebra.norm_def]
        simp only [map_add, map_mul]
        linear_combination (algebraMap O K q * algebraMap O K s * algebraMap O K s') * eτ
    have hdiff : quo z2.1 = quo z1.1 + algebraMap O K m •
        (⟨algebraMap O K q * algebraMap O K s, algebraMap O K q * algebraMap O K s'⟩ : Etau K τ) := by
      obtain ⟨h1a, h1b⟩ := hAB z1
      obtain ⟨h2a, h2b⟩ := hAB z2
      have ea := congrArg (algebraMap O K) hs
      have eb := congrArg (algebraMap O K) hs'
      simp only [map_mul, map_sub] at ea eb
      ext
      · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul, smul_eq_mul]
        apply mul_left_cancel₀ hQc
        linear_combination h2a - h1a - ea
      · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul, smul_eq_mul]
        apply mul_left_cancel₀ hQc
        linear_combination h2b - h1b - eb
    apply Subgroup.mem_subgroupOf.mpr
    apply hH _ (z1⁻¹ * z2).2 _ ((hint z1).2.mul hr)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, quo_mul', hdiff, mul_add, ← quo_mul', inv_mul_cancel,
      quo_one', mul_smul_comm]
  have hfin : Finite (Cint O τ ⧸ H.subgroupOf (Cint O τ)) := by
    let g : Set.range f → Cint O τ ⧸ H.subgroupOf (Cint O τ) :=
      fun s => QuotientGroup.mk (Classical.choose s.2)
    apply Finite.of_surjective g
    intro Q0
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q0
    refine ⟨⟨f z, z, rfl⟩, ?_⟩
    exact QuotientGroup.eq.mpr (key _ _ (Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)))
  show (H.subgroupOf (Cint O τ)).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

end

theorem isIntegral_star_quad {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {a b : K}
    {x : QuadraticAlgebra K a b} (hx : IsIntegral O x) : IsIntegral O (star x) := by
  let f : QuadraticAlgebra K a b →ₐ[O] QuadraticAlgebra K a b :=
    { starRingEnd (QuadraticAlgebra K a b) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K a b)]
        ext <;> simp [starRingEnd_apply] }
  exact hx.map f

section

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem intE_fg (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) :
    (Subalgebra.toSubmodule (integralClosure O (Etau K τ))).FG := by
  classical
  obtain ⟨c, hc, hcx⟩ := int_denom h hτ
  haveI := h.frac
  have hQc : algebraMap O K c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  refine Submodule.FG.of_le (Submodule.fg_span (R := O) (Set.toFinite
    ({(algebraMap O K c)⁻¹ • (1 : Etau K τ), (algebraMap O K c)⁻¹ • (QuadraticAlgebra.omega : Etau K τ)} :
      Set (Etau K τ)))) ?_
  intro x hx
  have hx' : IsIntegral O x := hx
  obtain ⟨a, b, ha, hb⟩ := hcx x hx'
  have hxeq : x = a • ((algebraMap O K c)⁻¹ • (1 : Etau K τ)) +
      b • ((algebraMap O K c)⁻¹ • (QuadraticAlgebra.omega : Etau K τ)) := by
    rw [← algebraMap_smul K a, ← algebraMap_smul K b, smul_smul, smul_smul, ← ha, ← hb]
    ext
    · simp
      field_simp
    · simp
      field_simp
  rw [hxeq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end

end UpperTheory.V.Z.Sym.Loc
