import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Carver
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pf_complete {O F : Type} [CommRing O] [NormedField F] [Algebra O F] [FaithfulSMul O F] (p : O)
    [IsPrecomplete (Ideal.span {p}) O] (h1 : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O F).range)
    (hp : ‖algebraMap O F p‖ = 1 / 2) : CompleteSpace F := by
  have hinj := FaithfulSMul.algebraMap_injective O F
  have hp0 : algebraMap O F p ≠ 0 := by
    intro h
    rw [h, norm_zero] at hp
    norm_num at hp
  have hmem : ∀ (n : ℕ) (a : O), a ∈ Ideal.span {p} ^ n ↔ ‖algebraMap O F a‖ ≤ (1 / 2) ^ n := by
    intro n a
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow, hp]
      exact mul_le_of_le_one_right (by positivity) ((h1 _).2 ⟨c, rfl⟩)
    · intro h
      obtain ⟨c, hc⟩ := (h1 (algebraMap O F a / algebraMap O F p ^ n)).1 (by
        rw [norm_div, norm_pow, hp]
        exact div_le_one_of_le₀ h (by positivity))
      refine ⟨c, hinj ?_⟩
      rw [map_mul, map_pow, hc, mul_div_cancel₀ _ (pow_ne_zero _ hp0)]
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n) (fun n => by positivity)
    fun u hu => ?_
  have ha : ∀ n, ∃ a : O, algebraMap O F a = u n - u 0 := fun n => (h1 _).1 (by
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le)
  choose a ha using ha
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) a (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, map_sub, ha, ha, sub_sub_sub_cancel_right,
      ← dist_eq_norm]
    exact (hu m m n le_rfl hmn).le)
  refine ⟨u 0 + algebraMap O F L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, map_sub, ha] at this
  rwa [← sub_sub]

private theorem pf_spectral {O F K : Type} [CommRing O] [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] [Algebra O F] [Field K] [Algebra O K] [Algebra F K] [IsScalarTower O F K]
    [Algebra.IsAlgebraic F K] (h1 : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O F).range) :
    ∃ w : AbsoluteValue K ℝ, ∀ x, w x ≤ 1 → IsIntegral O x := by
  letI : NormedField K := spectralNorm.normedField F K
  refine ⟨NormedField.toAbsoluteValue K, fun y hy => ?_⟩
  have hyK : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have h : spectralNorm F K y ≤ 1 := hy
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyK)] at h
  have hl : minpoly F y ∈ Polynomial.lifts (algebraMap O F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact (h1 _).1 (h n)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyK)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq, minpoly.aeval]

private theorem pf_abs (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] :
    ∃ w : AbsoluteValue K ℝ, ∀ x, w x ≤ 1 → IsIntegral O x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  have hpm : p ∈ maximalIdeal O := hmax ▸ Ideal.mem_span_singleton_self p
  obtain ⟨w, hw, hw1, hwa⟩ := GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing O (FractionRing O)
    hp.ne_zero hpm (r := 1 / 2) (by norm_num) (by norm_num)
  letI : NontriviallyNormedField (FractionRing O) :=
    { w.toNormedField with
      non_trivial := ⟨(algebraMap O (FractionRing O) p)⁻¹, by
        change 1 < w (algebraMap O (FractionRing O) p)⁻¹
        rw [map_inv₀, hwa]
        norm_num⟩ }
  haveI : IsUltrametricDist (FractionRing O) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hw
  haveI : IsPrecomplete (Ideal.span {p}) O := hmax ▸ inferInstance
  haveI : CompleteSpace (FractionRing O) := pf_complete p hw1 hwa
  letI : Algebra (FractionRing O) K := FractionRing.liftAlgebra O K
  haveI : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  haveI : Algebra.IsAlgebraic (FractionRing O) K := Algebra.IsAlgebraic.extendScalars
    (IsFractionRing.injective O (FractionRing O))
  exact pf_spectral (F := FractionRing O) hw1

private theorem pf_unit {O X σ : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {U : MvPowerSeries σ O}
    (hU : U ∈ wtPart O wt 0) (hu : IsUnit U) : ∃ G ∈ wtPart O wt 0, U * G = 1 := by
  classical
  obtain ⟨G, hG⟩ := hu.exists_right_inv
  refine ⟨wcomp O wt 0 G, wcomp_mem O wt 0 G, ?_⟩
  ext n
  by_cases hn : Finsupp.weight wt n = 0
  · rw [← hG, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases h1 : Finsupp.weight wt q.1 = 0
    · rw [coeff_wcomp, if_pos]
      rwa [← Finset.HasAntidiagonal.mem_antidiagonal.1 hq, map_add, h1, zero_add] at hn
    · rw [hU _ h1, zero_mul, zero_mul]
  · rw [one_mem_wtPart O wt n hn]
    exact mul_mem_wtPart O wt hU (wcomp_mem O wt 0 G) n (by rwa [add_zero])

private theorem pf_monomial {O σ S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (f : MvPowerSeries σ O →ₐ[O] S) (m : σ →₀ ℕ) :
    f (monomial m 1) = m.prod fun s k => f (MvPowerSeries.X s) ^ k := by
  rw [← MvPolynomial.coe_monomial, GlobalTheory.algHom_coe_mvPolynomial, MvPolynomial.aeval_monomial, map_one, one_mul]

private theorem pf_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add, ofAdd_add,
      map_mul, Units.val_mul]
    ring
  | single i k =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.weight_single, ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val, mul_pow]

private theorem pf_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem pf_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  obtain ⟨s, hs⟩ := pf_approx wt F n
  have := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  simpa [h] using this

section Core

variable {O X R K : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
  [Field K] [Algebra O K] (ξ : W.A →ₐ[O] K)

private theorem pf_zprod (m : W.σ →₀ ℕ) :
    ((m.prod fun s k => W.zA s ^ k : W.A) : R) = W.π (monomial m 1) := by
  rw [pf_monomial]
  exact map_finsuppProd W.A.val _ _

private theorem pf_nonint (n : W.σ →₀ ℕ) (hn : n ≠ 0) (h0 : Finsupp.weight W.wt n = 0)
    (ha : (n.prod fun s k => ξ (W.zA s) ^ k) ≠ 0) :
    ¬ IsIntegral O (n.prod fun s k => ξ (W.zA s) ^ k)⁻¹ := by
  classical
  rintro ⟨p, hp, hpa⟩
  have hu : (n.prod fun s k => ξ (W.zA s) ^ k) = ξ (n.prod fun s k => W.zA s ^ k) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hu] at ha hpa
  set u : W.A := n.prod fun s k => W.zA s ^ k with hudef
  letI : Invertible (ξ u)⁻¹ := invertibleOfNonzero (inv_ne_zero ha)
  have h1 : Polynomial.aeval (ξ u) p.reverse = 0 := by
    have := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap O K) (ξ u)⁻¹ p).2 hpa
    rwa [invOf_eq_inv, inv_inv] at this
  have hU : (monomial n 1 : MvPowerSeries W.σ O) ∈ wtPart O W.wt 0 := fun d hd => by
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hd h0
  have hU' : Polynomial.aeval (monomial n 1 : MvPowerSeries W.σ O) p.reverse ∈ wtPart O W.wt 0 := by
    have : Algebra.adjoin O {(monomial n 1 : MvPowerSeries W.σ O)} ≤
        SetLike.GradeZero.subalgebra (wtPart O W.wt) := Algebra.adjoin_le (Set.singleton_subset_iff.2 hU)
    exact this (Polynomial.aeval_mem_adjoin_singleton O _)
  have hunit : IsUnit (Polynomial.aeval (monomial n 1 : MvPowerSeries W.σ O) p.reverse) := by
    rw [isUnit_iff_constantCoeff, Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id O) (ψ := constantCoeff)
      (by ext a; simp [MvPowerSeries.algebraMap_apply])]
    have : constantCoeff (monomial n 1 : MvPowerSeries W.σ O) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hn.symm]
    rw [this, Polynomial.map_id, ← Polynomial.coeff_zero_eq_aeval_zero, Polynomial.coeff_zero_reverse, hp.leadingCoeff]
    exact isUnit_one
  obtain ⟨G, hG, hG1⟩ := pf_unit W.wt hU' hunit
  have h2 : Polynomial.aeval u p.reverse * (⟨W.π G, W.part_le_A ⟨G, hG, rfl⟩⟩ : W.A) = 1 := by
    apply Subtype.ext
    have h3 : ((Polynomial.aeval u p.reverse : W.A) : R) =
        W.π (Polynomial.aeval (monomial n 1 : MvPowerSeries W.σ O) p.reverse) := by
      rw [← Polynomial.aeval_algHom_apply, ← pf_zprod]
      exact (Polynomial.aeval_algHom_apply W.A.val u _).symm
    rw [Subalgebra.coe_mul, h3, ← map_mul, hG1, map_one, Subalgebra.coe_one]
  have h4 := congrArg ξ h2
  rw [map_mul, ← Polynomial.aeval_algHom_apply, h1, zero_mul, map_one] at h4
  exact zero_ne_one h4

variable [Module.Free ℤ X] [Module.Finite ℤ X] {B : Type} [CommRing B] [Algebra O B] (ι : B →ₐ[O] K)
  (t : Multiplicative X →* Kˣ) (g : MvPowerSeries W.σ O →ₐ[O] B)

private theorem pf_step (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (I J : Ideal B) (S : Set (W.σ →₀ ℕ)) (j : X) (hS : ∀ n ∈ S, Finsupp.weight W.wt n = j)
    (hJ : ∀ n ∈ S, g (monomial n 1) ∈ J)
    (hI : ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ I)
    (F : MvPowerSeries W.σ O) (hF : ∀ n, n ∉ S → coeff n F = 0) (x : W.A) (hx : (x : R) = W.π F) :
    ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ I * J := by
  obtain ⟨μ, hμ, h⟩ := part_span O R X W S j hS
  obtain ⟨b, hb, rfl⟩ := h F hF
  let β : (W.σ →₀ ℕ) → W.A := fun m => ⟨W.π (b m), W.part_le_A ⟨b m, hb m, rfl⟩⟩
  choose c hc hc' using fun m => hI (b m) (hb m) (β m) rfl
  have hx' : x = ∑ m ∈ μ, β m * m.prod fun s k => W.zA s ^ k := by
    apply Subtype.ext
    rw [hx, map_sum, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subalgebra.coe_mul, pf_zprod, map_mul]
  refine ⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩
  · rw [hx', map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, map_mul, hc, pf_monomial, map_finsuppProd, map_finsuppProd]
    simp only [map_pow, hg]
    rw [pf_prod W.wt t (fun s => ξ (W.zA s)), hS m (hμ hm)]
    ring
  · rw [map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, ← sub_mul]
    exact Ideal.mul_mem_mul (hc' m) (hJ m (hμ hm))

private theorem pf_agree (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (j : X) (F : MvPowerSeries W.σ O) (hF : F ∈ wtPart O W.wt j)
    (x : W.A) (hx : (x : R) = W.π F) : ι (g F) = t (Multiplicative.ofAdd j) * ξ x := by
  classical
  have hQ : ∀ N : ℕ, ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b →
      ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ N := by
    intro N
    induction N with
    | zero =>
      intro b hb x hx
      obtain ⟨c, hc⟩ := h0 x ⟨b, hb, hx.symm⟩
      exact ⟨c, hc, by simp⟩
    | succ N ih =>
      intro b hb x hx
      obtain ⟨c, hc, hc'⟩ := pf_step W ξ ι t g hg (J ^ N) J {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0} 0
        (fun n hn => hn.1) (fun n hn => by
          have := GlobalTheory.algHom_sub_constantCoeff_mem g hJ (monomial n 1)
          rwa [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hn.2.symm, map_zero,
            sub_zero] at this) ih
        (b - algebraMap O _ (constantCoeff b)) (fun n hn => by
          rw [map_sub, MvPowerSeries.algebraMap_apply, coeff_C]
          split_ifs with h
          · subst h; simp
          · rw [sub_zero]
            exact hb n fun h' => hn ⟨h', h⟩)
        (x - algebraMap O _ (constantCoeff b)) (by
          rw [map_sub, AlgHom.commutes, ← hx]; rfl)
      refine ⟨c + algebraMap O B (constantCoeff b), ?_, ?_⟩
      · rw [map_add, hc, AlgHom.commutes, map_sub, AlgHom.commutes]
        simp
      · rw [map_sub, AlgHom.commutes, sub_sub, add_comm] at hc'
        rwa [pow_succ]
  obtain ⟨c, hc, hc'⟩ := pf_step W ξ ι t g hg ⊥ ⊤ {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
    (fun _ _ => trivial) (fun b hb x hx => by
      obtain ⟨c, hc, -⟩ := hQ 0 b hb x hx
      refine ⟨c, hc, ?_⟩
      rw [Ideal.mem_bot, sub_eq_zero]
      refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun N => ?_
      obtain ⟨c', hc1, hc2⟩ := hQ N b hb x hx
      rwa [hι (hc.trans hc1.symm)]) F hF x hx
  rw [Ideal.bot_mul, Ideal.mem_bot, sub_eq_zero] at hc'
  rw [hc', hc]

private theorem pf_factor [DecidableEq X] (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) :
    ∃ f : R →ₐ[O] B, (ι.comp f).comp W.A.val = act W.gr t ξ := by
  have key := pf_agree W ξ ι t g hι hg J hJ h0
  have hker : ∀ F ∈ RingHom.ker W.π, g F = 0 := by
    intro F hF
    refine pf_vanish W.wt J g hJ F fun j => hι ?_
    have h1 : W.π (wcomp O W.wt j F) = 0 := W.homog F hF j
    rw [key j _ (wcomp_mem O W.wt j F) 0 h1.symm, map_zero, map_zero, mul_zero]
  let f : R →ₐ[O] B := (Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf : ∀ F, f (W.π F) = g F := by
    intro F
    have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) = Ideal.Quotient.mk _ F := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [f, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨f, AlgHom.ext fun x => ?_⟩
  induction x using DirectSum.Decomposition.inductionOn W.gr with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | @homogeneous j x =>
    obtain ⟨x, hx⟩ := x
    rw [act_of_mem W.gr t ξ hx]
    obtain ⟨F, hF, hFx⟩ := hx
    have hFx' : (x : R) = W.π F := hFx.symm
    rw [← key j F hF x hFx', ← hf, ← hFx']
    rfl

end Core

theorem UpperTheory.V.Alg.points_finite :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (ξ : W.A →ₐ[O] K),
      ((W.gr 0).map ξ.toLinearMap).FG →
      ∃ (t : Multiplicative X →* Kˣ) (Ξ : R →ₐ[O] K), Ξ.comp W.A.val = act W.gr t ξ ∧ Module.Finite O Ξ.range := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _ K _ _ _ _ _ ξ hfg
  obtain ⟨w, hw⟩ := pf_abs O K
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  have hlt : ∀ a : K, (a ≠ 0 → ¬ IsIntegral O a⁻¹) → w a < 1 := by
    intro a ha
    by_cases h0 : a = 0
    · simp [h0]
    · by_contra h
      refine ha h0 (hw _ ?_)
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (not_lt.1 h)
  have hwp : w (algebraMap O K p) < 1 := hlt _ fun _ h => by
    haveI : IsLocalHom (algebraMap O (integralClosure O K)) := inferInstance
    refine hp.not_isUnit (IsLocalHom.map_nonunit (f := algebraMap O (integralClosure O K)) p
      (IsUnit.of_mul_eq_one (⟨_, h⟩ : integralClosure O K) (Subtype.ext ?_)))
    exact mul_inv_cancel₀ hp0
  obtain ⟨t, ht⟩ : ∃ t : Multiplicative X →* Kˣ,
      ∀ s, w ((t (Multiplicative.ofAdd (W.wt s)) : K) * ξ (W.zA s)) < 1 := by
    letI : NormedField K := w.toNormedField
    exact carver W.σ X W.wt K (fun s => ξ (W.zA s)) ⟨_, hp0, hwp.ne⟩
      fun n hn h0 => hlt _ (pf_nonint W ξ n hn h0)
  set y : W.σ → K := fun s => (t (Multiplicative.ofAdd (W.wt s)) : K) * ξ (W.zA s) with hy
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O (y s ^ n / algebraMap O K p) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hp0) (ht s)
    refine ⟨n, hw _ ?_⟩
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hn.le (w.nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set K := (T : Set K) ∪ Set.range y ∪ Set.range fun s => y s ^ e s / algebraMap O K p
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · refine IsIntegral.of_mem_of_fg ((SetLike.GradeZero.subalgebra W.gr).map ξ) hfg x ?_
      have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      exact this
    · exact hw _ (ht s).le
    · exact he s
  let B : Subalgebra O K := Algebra.adjoin O G
  haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  haveI : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  let yB : W.σ → B := fun s => ⟨y s, Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))⟩
  have hyB : ∀ s, yB s ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : yB s ^ e s = algebraMap O B p *
        ⟨y s ^ e s / algebraMap O K p, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ :=
      Subtype.ext (mul_div_cancel₀ _ hp0).symm
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := pf_factor W ξ B.val t (GlobalTheory.mvEvalAdic O J yB hyB) Subtype.val_injective
    (fun s => by rw [GlobalTheory.mvEvalAdic_X]; rfl) J (fun s => by rw [GlobalTheory.mvEvalAdic_X]; exact hyB s)
    (fun x hx => by
      have h1 : ξ x ∈ Submodule.span O (T : Set K) := hT ▸ Submodule.mem_map_of_mem hx
      have h2 : Submodule.span O (T : Set K) ≤ B.toSubmodule :=
        Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
      exact ⟨⟨ξ x, h2 h1⟩, rfl⟩)
  refine ⟨t, B.val.comp f, hf, ?_⟩
  have hle : (B.val.comp f).range ≤ B := by
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  exact Module.Finite.of_injective (Subalgebra.inclusion hle).toLinearMap (Subalgebra.inclusion_injective hle)
