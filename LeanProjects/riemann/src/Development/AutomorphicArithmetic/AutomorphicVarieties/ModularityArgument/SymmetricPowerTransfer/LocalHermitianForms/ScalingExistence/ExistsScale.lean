import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.Loc.FU

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

private theorem intL_fg (h : IsLoc O Δ) : (Subalgebra.toSubmodule (integralClosure O (Lsq K Δ))).FG := by
  classical
  obtain ⟨u, t, ht, hΔ⟩ := h.even
  have hd : Δ * t⁻¹ ^ 2 = algebraMap O K u := by
    rw [hΔ]
    field_simp
  refine ⟨({(⟨1, 0⟩ : Lsq K Δ), (⟨0, t⁻¹⟩ : Lsq K Δ)} : Finset (Lsq K Δ)), ?_⟩
  ext x
  rw [Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_pair, Subalgebra.mem_toSubmodule,
    mem_integralClosure_iff]
  have key := (descent O K Δ h t⁻¹ u hd x).1
  change _ ↔ IsInt O x
  rw [key]
  constructor
  · rintro ⟨c, d, rfl⟩
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
      QuadraticAlgebra.im_smul]
    refine ⟨⟨c, by simp [Algebra.smul_def]⟩, d, by simp [Algebra.smul_def]; ring⟩
  · rintro ⟨⟨c, hc⟩, d, hd'⟩
    refine ⟨c, d, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul]
      simp [Algebra.smul_def, hc]
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul]
      simp [Algebra.smul_def, hd']
      ring

private theorem star_smul_lsq (c : O) (y : Lsq K Δ) : star (c • y) = c • star y := by
  ext <;> simp [smul_neg]

private theorem eq_of_smul_eq_smul_of_ne_zero (h : IsLoc O Δ) {N : O} (hN : N ≠ 0) {v w : Lsq K Δ}
    (hvw : N • v = N • w) : v = w := by
  haveI := h.frac
  have hNK : algebraMap O K N ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hN
  rw [← algebraMap_smul K N v, ← algebraMap_smul K N w] at hvw
  exact smul_right_injective (Lsq K Δ) hNK hvw

theorem fin_cosets (h : IsLoc O Δ) {N : O} (hN : N ≠ 0) :
    ∃ s : Finset (U3 Δ), ∀ x : U3 Δ, (∀ i j, IsIntegral O (N • (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)) →
      ∃ x' ∈ s, ∃ k ∈ KU O Δ, x = x' * k := by
  classical
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (intL_fg h)
  have hmem : ∀ v : Lsq K Δ, v ∈ Submodule.span O (Set.range g) ↔ IsIntegral O v := by
    intro v
    rw [hg, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  have hgi : ∀ k, IsIntegral O (g k) := fun k => (hmem _).1 (Submodule.subset_span ⟨k, rfl⟩)
  have hrep : ∀ v : Lsq K Δ, IsIntegral O v → ∃ c : Fin r → O, ∑ k, c k • g k = v := by
    intro v hv
    exact (Submodule.mem_span_range_iff_exists_fun O).1 ((hmem v).2 hv)
  choose! coef hcoef using hrep
  haveI : Finite (O ⧸ Ideal.span {N ^ 2}) := finite_quot_span h (pow_ne_zero 2 hN)
  let code : U3 Δ → Fin 3 → Fin 3 → Fin r → O ⧸ Ideal.span {N ^ 2} := fun x i j k =>
    Ideal.Quotient.mk _ (coef (N • (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) k)
  let P : U3 Δ → Prop := fun x =>
    ∀ i j, IsIntegral O (N • (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j)
  have hC : (code '' {x | P x}).Finite := Set.toFinite _
  have hex : ∀ c ∈ code '' {x | P x}, ∃ x, P x ∧ code x = c := fun c hc => hc
  choose! rep hrep' using hex
  refine ⟨(hC.image rep).toFinset, ?_⟩
  intro x hx
  have hcx : code x ∈ code '' {x | P x} := ⟨x, hx, rfl⟩
  obtain ⟨hPx', hcode⟩ := hrep' (code x) hcx
  refine ⟨rep (code x), (Set.Finite.mem_toFinset _).2 ⟨code x, hcx, rfl⟩, (rep (code x))⁻¹ * x, ?_,
    (mul_inv_cancel_left _ _).symm⟩
  set x' := rep (code x) with hx'
  have hdiff : ∀ l j, ∃ w : Lsq K Δ, IsIntegral O w ∧
      (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j
        = (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j + N • w := by
    intro l j
    have hc1 := hcoef _ (hx l j)
    have hc2 := hcoef _ (hPx' l j)
    have hd : ∀ k, ∃ d : O, coef (N • (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j) k
        - coef (N • (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j) k = N ^ 2 * d := by
      intro k
      have e1 := congrFun (congrFun (congrFun hcode l) j) k
      have e2 : coef (N • (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j) k
          - coef (N • (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l j) k ∈ Ideal.span {N ^ 2} := by
        rw [← Ideal.Quotient.eq]
        exact e1.symm
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 e2
      exact ⟨d, by rw [← hd, mul_comm]⟩
    choose d hd using hd
    refine ⟨∑ k, d k • g k, ?_, ?_⟩
    · rw [← mem_integralClosure_iff]
      exact Subalgebra.sum_mem _ fun k _ =>
        Subalgebra.smul_mem _ ((mem_integralClosure_iff _ _).2 (hgi k)) _
    · rw [← sub_eq_iff_eq_add']
      apply eq_of_smul_eq_smul_of_ne_zero h hN
      rw [smul_sub, ← hc1, ← hc2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sub_smul, hd k, smul_smul, smul_smul, pow_two]
  choose W hWi hW using hdiff
  have hstar : star (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
      = 1 := congrArg Subtype.val (inv_mul_cancel x')
  have hent : ∀ i j, IsIntegral O
      (((x'⁻¹ * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := by
    intro i j
    have e : ((x'⁻¹ * x : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j
        = (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j
          + ∑ l, star (N • (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) l i) * W l j := by
      rw [← hstar]
      change (star (x' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (x : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) i j = _
      simp only [Matrix.mul_apply, Matrix.star_apply, hW, mul_add, Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_smul_lsq, smul_mul_assoc, mul_smul_comm]
    rw [e, ← mem_integralClosure_iff]
    refine Subalgebra.add_mem _ ?_ (Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ ?_ ?_)
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · exact (mem_integralClosure_iff _ _).2 (isIntegral_star_quad (hPx' l i))
    · exact (mem_integralClosure_iff _ _).2 (hWi l j)
  intro i j
  exact ⟨hent i j, isIntegral_star_quad (hent i j)⟩

private theorem int_of_tr {a b : K} (e : QuadraticAlgebra K a b) (t n : O) (ht : algebraMap O K t = trace e)
    (hn : algebraMap O K n = QuadraticAlgebra.norm e) : IsIntegral O e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, by monicity!, ?_⟩
  have := sq_sub_trace_smul_add_norm_eq_zero (z := e)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K a b), ht, hn]
  rw [← Algebra.smul_def]
  exact this

private theorem int_of_norm (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ) (n : O)
    (hn : algebraMap O K n = QuadraticAlgebra.norm e) : IsIntegral O e := by
  haveI := h.frac
  set t := QuadraticAlgebra.trace e with ht_def
  have key : 4 * algebraMap O K n = t ^ 2 - (τ ^ 2 - 4) * e.im ^ 2 := by
    rw [hn, ht_def, trace_def, norm_def]
    ring
  have htO : ∃ c : O, algebraMap O K c = t := by
    by_cases ht0 : t = 0
    · exact ⟨0, by simp [ht0]⟩
    rcases ValuationRing.isInteger_or_isInteger O t with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, hc⟩
    by_cases hcu : IsUnit c
    · refine ⟨((hcu.unit⁻¹ : Oˣ) : O), ?_⟩
      rw [map_units_inv (algebraMap O K) hcu.unit, IsUnit.unit_spec, hc, inv_inv]
    exfalso
    have hcm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal c).2 hcu
    have hc0' : algebraMap O K c ≠ 0 := by
      rw [hc]
      exact inv_ne_zero ht0
    have hct : algebraMap O K c * t = 1 := by
      rw [hc]
      exact inv_mul_cancel₀ ht0
    have hm : (1 - 4 * n * c ^ 2) - 1 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      have e1 : (1 - 4 * n * c ^ 2) - 1 ^ 2 = (-(4 * n * c)) * c := by ring
      rw [e1]
      exact Ideal.mul_mem_left _ _ hcm
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * n * c ^ 2) 1 isUnit_one hm
    have hr' : algebraMap O K r ^ 2 = 1 - 4 * algebraMap O K n * algebraMap O K c ^ 2 := by
      rw [← map_pow, hr]
      simp only [map_sub, map_one, map_mul, map_pow, map_ofNat]
    have hD : (τ ^ 2 - 4) * (algebraMap O K c * e.im) ^ 2 = algebraMap O K r ^ 2 := by
      linear_combination (-1) * hr' + (algebraMap O K c) ^ 2 * key + (algebraMap O K c * t + 1) * hct
    by_cases him : e.im = 0
    · have hr0 : algebraMap O K r ^ 2 = 0 := by
        rw [← hD, him]
        ring
      have hr00 : r = 0 := by
        have h3 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 hr0
        exact (map_eq_zero_iff _ (IsFractionRing.injective O K)).1 h3
      apply hcu
      refine IsUnit.of_mul_eq_one (4 * n * c) ?_
      rw [hr00] at hr
      linear_combination hr
    · apply hτ
      refine ⟨algebraMap O K r / (algebraMap O K c * e.im), ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero hc0' him) (mul_ne_zero hc0' him))]
      linear_combination hD
  obtain ⟨c, hc⟩ := htO
  exact int_of_tr e c n hc hn

private theorem exists_scale [IsFractionRing O K] {ι : Type} [Finite ι] (f g : ι → K) {N : O}
    (hfg : ∀ i j, ∃ r : O, algebraMap O K r = algebraMap O K N * (f i * g j)) :
    ∃ s : K, s ≠ 0 ∧ (∀ i, ∃ r : O, algebraMap O K r = s * f i) ∧
      ∀ j, ∃ r : O, algebraMap O K r = algebraMap O K N * (s⁻¹ * g j) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) f
  choose p hp using hb
  have hb0 : algebraMap O K (b : O) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  by_cases hall : ∀ i, f i = 0
  · obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) g
    choose q hq using hc
    have hc0 : algebraMap O K (c : O) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
    refine ⟨(algebraMap O K c)⁻¹, inv_ne_zero hc0, fun i => ⟨0, by simp [hall i]⟩, fun j => ⟨N * q j, ?_⟩⟩
    rw [map_mul, hq j, inv_inv, Algebra.smul_def]
  push_neg at hall
  obtain ⟨i1, hi1⟩ := hall
  haveI : Nonempty ι := ⟨i1⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => IsDiscreteValuationRing.addVal O (p i))
  have hp0 : p i0 ≠ 0 := by
    intro h0
    have h1 := hi0 i1
    rw [h0, IsDiscreteValuationRing.addVal_zero, top_le_iff,
      IsDiscreteValuationRing.addVal_eq_top_iff] at h1
    apply hi1
    have h2 := hp i1
    rw [h1, map_zero, Algebra.smul_def] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  have hf0 : f i0 ≠ 0 := by
    intro h0
    apply hp0
    apply IsFractionRing.injective O K
    rw [hp, h0, smul_zero, map_zero]
  refine ⟨(f i0)⁻¹, inv_ne_zero hf0, fun i => ?_, fun j => ?_⟩
  · obtain ⟨k, hk⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 (hi0 i)
    refine ⟨k, ?_⟩
    have e1 := hp i
    have e2 := hp i0
    rw [hk, map_mul, Algebra.smul_def] at e1
    rw [Algebra.smul_def] at e2
    rw [e2] at e1
    rw [eq_inv_mul_iff_mul_eq₀ hf0]
    apply mul_left_cancel₀ hb0
    linear_combination e1
  · rw [inv_inv]
    exact hfg i0 j

theorem tor_bound (h : IsLoc O Δ) (hτ : τ ^ 2 - 4 ≠ 0) (N : O) {ι : Type} [Finite ι] (T : ι → Etau K τ)
    (hT : ∀ i j, IsIntegral O (N • (T i * star (T j)))) :
    ∃ z : (Etau K τ)ˣ, ∀ i, IsIntegral O (N • (quo z * T i)) := by
  classical
  haveI := h.frac
  have h2 : (2 : K) ≠ 0 := by
    have h3 := h.two.map (algebraMap O K)
    rw [map_ofNat] at h3
    exact h3.ne_zero
  have hK : ∀ c : K, IsIntegral O c → ∃ r : O, algebraMap O K r = c := fun c hc =>
    IsIntegrallyClosed.isIntegral_iff.1 hc
  have hKE : ∀ c : K, IsIntegral O (algebraMap K (Etau K τ) c) → ∃ r : O, algebraMap O K r = c := by
    intro c hc
    apply hK
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Etau K τ))
      (algebraMap K (Etau K τ)).injective (x := c)).1 hc
  have hn : ∀ i, ∃ r : O, algebraMap O K r = algebraMap O K N * QuadraticAlgebra.norm (T i) := by
    intro i
    apply hKE
    have h3 := hT i i
    rwa [← algebraMap_norm_eq_mul_star, Algebra.smul_def,
      IsScalarTower.algebraMap_apply O K (Etau K τ), ← map_mul] at h3
  by_cases hsq : IsSquare (τ ^ 2 - 4)
  swap
  · refine ⟨1, fun i => ?_⟩
    rw [quo_one', one_mul]
    obtain ⟨m, hm⟩ := hn i
    apply int_of_norm h hsq (N • T i) (N * m)
    have e1 : QuadraticAlgebra.norm (N • T i) = (algebraMap O K N) ^ 2 * QuadraticAlgebra.norm (T i) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O K (Etau K τ), map_mul, QuadraticAlgebra.norm_algebraMap]
    rw [e1, map_mul, hm]
    ring
  obtain ⟨d, hd⟩ := hsq
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hd, mul_zero]
  obtain ⟨i2, hi2⟩ : ∃ i : K, 2 * i = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2⟩
  obtain ⟨r1, hr1def⟩ : ∃ r : K, r = (τ + d) * i2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2def⟩ : ∃ r : K, r = (τ - d) * i2 := ⟨_, rfl⟩
  have hr1 : r1 * r1 = (-1 : K) • (1 : K) + τ • r1 := by
    simp only [smul_eq_mul, mul_one]
    rw [hr1def]
    linear_combination (τ * (τ + d) * i2 - (2 * i2 + 1)) * hi2 - i2 ^ 2 * hd
  have hr2 : r2 * r2 = (-1 : K) • (1 : K) + τ • r2 := by
    simp only [smul_eq_mul, mul_one]
    rw [hr2def]
    linear_combination (τ * (τ - d) * i2 - (2 * i2 + 1)) * hi2 - i2 ^ 2 * hd
  have hsum : r1 + r2 = τ := by
    rw [hr1def, hr2def]
    linear_combination τ * hi2
  have hprod : r1 * r2 = 1 := by
    rw [hr1def, hr2def]
    linear_combination (2 * i2 + 1) * hi2 + i2 ^ 2 * hd
  have hr12 : r1 - r2 = d := by
    rw [hr1def, hr2def]
    linear_combination d * hi2
  obtain ⟨φ1, hφ1⟩ : ∃ φ : Etau K τ →ₐ[K] K, ∀ x, φ x = x.re + x.im * r1 :=
    ⟨QuadraticAlgebra.lift ⟨r1, hr1⟩, fun x => by simp [QuadraticAlgebra.lift_apply_apply, smul_eq_mul]⟩
  obtain ⟨φ2, hφ2⟩ : ∃ φ : Etau K τ →ₐ[K] K, ∀ x, φ x = x.re + x.im * r2 :=
    ⟨QuadraticAlgebra.lift ⟨r2, hr2⟩, fun x => by simp [QuadraticAlgebra.lift_apply_apply, smul_eq_mul]⟩
  have hstar1 : ∀ x, φ1 (star x) = φ2 x := by
    intro x
    rw [hφ1, hφ2, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    linear_combination (-x.im) * hsum
  have hstar2 : ∀ x, φ2 (star x) = φ1 x := by
    intro x
    rw [hφ1, hφ2, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    linear_combination (-x.im) * hsum
  have htr : ∀ x : Etau K τ, QuadraticAlgebra.trace x = φ1 x + φ2 x := by
    intro x
    rw [hφ1, hφ2, trace_def]
    linear_combination (-x.im) * hsum
  have hnorm : ∀ x : Etau K τ, QuadraticAlgebra.norm x = φ1 x * φ2 x := by
    intro x
    rw [hφ1, hφ2, norm_def]
    linear_combination (-(x.re * x.im)) * hsum + (-(x.im * x.im)) * hprod
  have hsm : ∀ (φ : Etau K τ →ₐ[K] K) (y : Etau K τ), φ (N • y) = algebraMap O K N * φ y := by
    intro φ y
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O K (Etau K τ), map_mul, AlgHom.commutes,
      Algebra.algebraMap_self_apply]
  have hfg : ∀ i j, ∃ r : O, algebraMap O K r = algebraMap O K N * (φ1 (T i) * φ2 (T j)) := by
    intro i j
    apply hK
    have hi := (hT i j).map (φ1.restrictScalars O)
    rw [AlgHom.restrictScalars_apply, hsm, map_mul, hstar1] at hi
    exact hi
  obtain ⟨s, hs0, hsf, hsg⟩ := exists_scale (fun i => φ1 (T i)) (fun j => φ2 (T j)) hfg
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Etau K τ, φ1 z = s ∧ φ2 z = 1 := by
    refine ⟨⟨1 - (s - 1) / d * r2, (s - 1) / d⟩, ?_, ?_⟩
    · rw [hφ1]
      have e1 : (1 - (s - 1) / d * r2) + (s - 1) / d * r1 = 1 + (s - 1) / d * (r1 - r2) := by ring
      rw [e1, hr12, div_mul_cancel₀ _ hd0]
      ring
    · rw [hφ2]
      ring
  have hzU : IsUnit z := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, hnorm, hz1, hz2, mul_one]
    exact hs0.isUnit
  have hq1 : φ1 (quo hzU.unit) = s := by
    rw [quo, map_mul, hstar1, map_units_inv, IsUnit.unit_spec, hz1, hz2, inv_one, mul_one]
  have hq2 : φ2 (quo hzU.unit) = s⁻¹ := by
    rw [quo, map_mul, hstar2, map_units_inv, IsUnit.unit_spec, hz1, hz2, one_mul]
  refine ⟨hzU.unit, fun i => ?_⟩
  obtain ⟨a1, ha1⟩ := hsf i
  obtain ⟨a2, ha2⟩ := hsg i
  obtain ⟨m, hm⟩ := hn i
  have hX1 : φ1 (N • (quo hzU.unit * T i)) = algebraMap O K N * (s * φ1 (T i)) := by
    rw [hsm, map_mul, hq1]
  have hX2 : φ2 (N • (quo hzU.unit * T i)) = algebraMap O K N * (s⁻¹ * φ2 (T i)) := by
    rw [hsm, map_mul, hq2]
  apply int_of_tr (N • (quo hzU.unit * T i)) (N * a1 + a2) (N * m)
  · rw [htr, hX1, hX2, map_add, map_mul, ha1, ha2]
  · rw [hnorm, hX1, hX2, map_mul, hm, hnorm (T i)]
    field_simp

end UpperTheory.V.Z.Sym.Loc.FU
