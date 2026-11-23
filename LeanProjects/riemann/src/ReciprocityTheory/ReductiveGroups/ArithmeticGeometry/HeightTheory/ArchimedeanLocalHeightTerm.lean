import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubstitutedEqIntegral

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem archimedean_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ) (sg : K →+* ℂ) :
    d.localHeightAtEmbedding (d.wx x) c sg =
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg F) -
        blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) +
        Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0)
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hmi := MvPolynomial.map_injective (σ := TVar d.D d.N) sg sg.injective
  have hFc0 : MvPolynomial.map sg F' ≠ 0 := (map_ne_zero_iff _ hmi).2 hFne
  have ha1c : MvPolynomial.map sg a1' ≠ 0 :=
    (map_ne_zero_iff _ hmi).2 (mul_ne_zero (by simpa using hκ3) ha10)
  have hb1c : MvPolynomial.map sg b1 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb10
  have ha2c : MvPolynomial.map sg a2 ≠ 0 := (map_ne_zero_iff _ hmi).2 ha20
  have hb2c : MvPolynomial.map sg b2 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb20
  have hFcmh := isMultiHomogeneous_map_ring _ F' hFmh sg
  obtain ⟨αa1, hαa10, hαa1⟩ := hintMH_map (hintMH_C_mul κ3 ha1) sg
  obtain ⟨αb1, hαb10, hαb1⟩ := hintMH_map hb1 sg
  obtain ⟨αa2, hαa20, hαa2⟩ := hintMH_map ha2 sg
  obtain ⟨αb2, hαb20, hαb2⟩ := hintMH_map hb2 sg
  have I1 := hint_fubini hn hFc0 hFcmh
  have Ia1 := hint_logInt_tail hn ha1c hαa1 hαa10 0
  have Ib1 := hint_logInt_tail hn hb1c hαb1 hαb10 0
  have Ia2 := hint_logInt_tail hn ha2c hαa2 hαa20 0
  have Ib2 := hint_logInt_tail hn hb2c hαb2 hαb20 0
  have hind : ∀ (z : BlockSphere d.D (d.N + 1))
      (q : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ) (α : Fin (d.D + 1) → ℕ),
      α 0 = 0 → IsMultiHomogeneous α q → ∀ t0 : Fin (d.N + 1) → ℂ,
      MvPolynomial.eval (hintPt t0 z) q = MvPolynomial.eval (hintPt 0 z) q := by
    intro z q α h0 hq t0
    refine hint_eval_indep hq h0 _ _ ?_
    rintro ⟨i, j⟩ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
    rfl

  have hpt : ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)),
      (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
        -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P)) =
        (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
            ∂(sphereProb (d.N + 1))) -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ +
          Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 ∧
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
    filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hb1c hαb1 hαb10 0,
      hint_ae_tail hn hb2c hαb2 hαb20 0, hint_ae_tail hn ha2c hαa2 hαa20 0] with z hz hb1z hb2z ha2z
    obtain ⟨hfin, hcard, hcl1, hcl2⟩ := hz
    set S := d.ST c sg (d.tOf z) with hS
    have hpe := congrArg (fun q => MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg q)) hpoly
    simp only [map_mul, MvPolynomial.map_C, MvPolynomial.eval_C] at hpe

    have hb1z' : d.evT sg 0 (d.tOf z) b1 ≠ 0 := by rw [hint_evT_eq]; exact hb1z
    have hprod1 := hcl1 ra a1' b1 0 hra0 hb10 hkey1 hb1z'
    have hPra : ∀ P ∈ S, P ra ≠ 0 := fun P _ => (map_ne_zero_iff P P.injective).2 hra0
    have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), P ra) ≠ 0 := by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      exact Finset.prod_ne_zero_iff.2 fun P hP => hPra P (hfin.mem_toFinset.1 hP)
    have ha1z : d.evT sg 0 (d.tOf z) a1' ≠ 0 := by
      intro h0; rw [h0, zero_div] at hprod1; exact hprod0 hprod1.symm
    rw [hint_evT_eq, hint_evT_eq] at hprod1
    rw [hint_evT_eq] at ha1z
    have hsum1 : ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [hint_log_finprod _ hfin _ hPra, ← hprod1, norm_div,
        Real.log_div (norm_ne_zero_iff.2 ha1z) (norm_ne_zero_iff.2 hb1z)]

    have hsk : sg κ ≠ 0 := (map_ne_zero sg).2 hκ
    have hlhs0 : sg κ * MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1') *
        MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hsk ha1z) ha2z
    rw [hpe] at hlhs0
    have hFXz : MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F')) ≠ 0 := by
      intro h0; apply hlhs0; rw [h0]; ring
    have hlogFX : Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      have hl := congrArg (fun w : ℂ => Real.log ‖w‖) hpe
      simp only [norm_mul] at hl
      rw [Real.log_mul (by positivity) (norm_ne_zero_iff.2 ha2z),
        Real.log_mul (norm_ne_zero_iff.2 hsk) (norm_ne_zero_iff.2 ha1z),
        Real.log_mul (by positivity) (norm_ne_zero_iff.2 hb1z),
        Real.log_mul (norm_ne_zero_iff.2 hFXz) (norm_ne_zero_iff.2 hb2z)] at hl
      linarith
    refine ⟨?_, hlogFX⟩

    have hlin : ∀ᵐ s ∂(sphereProb (d.N + 1)), ∀ P ∈ S,
        ∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j ≠ 0 :=
      (Filter.eventually_all_finite hfin).2 fun P _ => hint_lin_ae _ (d.hint_U_coord_ne hd c P)
    have hptU : ∀ᵐ s ∂(sphereProb (d.N + 1)),
        Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖ =
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
            Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
            ∑ P ∈ hfin.toFinset,
              Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
      filter_upwards [hlin] with s hs
      have haz' : d.evT sg (spherePoint s) (d.tOf z) a2 ≠ 0 := by
        rw [hint_evT_eq, hind z _ _ hαa20 hαa2]; exact ha2z
      have hq := hcl2 (F' * b2) a2 (spherePoint s) ha20 hkey2 haz'
      rw [hint_evT_eq, hint_evT_eq, map_mul, map_mul, hind z _ _ hαa20 hαa2,
        hind z (MvPolynomial.map sg b2) _ hαb20 hαb2] at hq
      have hL : ∀ P ∈ S, (∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        intro P hP
        have := hs P hP
        simpa [hintU, mul_comm] using this
      have hprod0' : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
          ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
        exact Finset.prod_ne_zero_iff.2 fun P hP => hL P (hfin.mem_toFinset.1 hP)
      have heq : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F') =
          MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) *
            (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
              ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) /
            MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2) := by
        rw [← hq]; field_simp
      rw [heq, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero ha2z hprod0')
        (norm_ne_zero_iff.2 hb2z), Real.log_mul (norm_ne_zero_iff.2 ha2z)
        (norm_ne_zero_iff.2 hprod0'), ← hint_log_finprod _ hfin _ hL,
        finsum_mem_eq_finite_toFinset_sum _ hfin]
      have : ∀ P ∈ hfin.toFinset, Real.log ‖∑ j, spherePoint s j *
          P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ =
          Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
        intro P _; simp [hintU, mul_comm]
      rw [Finset.sum_congr rfl this]; ring
    have hInt : ∀ P ∈ hfin.toFinset, Integrable (fun s : UnitSphereC (d.N + 1) =>
        Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖) (sphereProb (d.N + 1)) :=
      fun P _ => (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
        (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).1
    have hval : ∀ P ∈ hfin.toFinset, ∫ s, Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j *
        spherePoint s j‖ ∂(sphereProb (d.N + 1)) = Real.log ‖d.hintU c P‖ - (harmonic d.N : ℝ) / 2 := by
      intro P _
      have := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
        (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).2
      simpa using this
    have hintS : ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
        ∂(sphereProb (d.N + 1)) =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
          ∑ P ∈ hfin.toFinset, Real.log ‖d.hintU c P‖ - d.delc c * (harmonic d.N : ℝ) / 2 := by
      rw [integral_congr_ae hptU, integral_add (integrable_const _) (integrable_finset_sum _ hInt),
        integral_const, integral_finset_sum _ hInt, Finset.sum_congr rfl hval, Finset.sum_sub_distrib,
        Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, hcard]
      simp only [probReal_univ, one_smul, nsmul_eq_mul]
      ring

    have hPe : ∀ P : Ω c →+* ℂ, -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) =
        Real.log ‖d.hintU c P‖ - Real.log ‖P ra‖ := by
      intro P
      have hw := d.eq_ratio_base_smul hd c hmem
      have hn1 : d.nrm c d.wL (d.wx x c) P = ‖P ra‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
        conv_lhs => rw [hw]
        exact hd.nrm_smul c P _ (hd.w_mem _ c) (hd.w_base c) hra0
      have hpos := hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)
      have hU := d.hint_one_le_U hd c P
      rw [hn1, d.hint_be_eq hd c P, mul_comm ‖P ra‖, mul_div_mul_left _ _ hpos.ne',
        Real.log_div (norm_ne_zero_iff.2 ((map_ne_zero P).2 hra0)) (by linarith)]
      ring
    change ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) = _
    have hsum1' : ∑ P ∈ hfin.toFinset, Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]; exact hsum1
    rw [finsum_mem_congr rfl fun P _ => hPe P, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_sub_distrib, hsum1', hintS, hlogFX]
    ring

  have IFX : Integrable (fun z : BlockSphere d.D (d.N + 1) =>
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖)
      (blockSphereProb d.D (d.N + 1)) := by
    refine (((((integrable_const (Real.log ‖sg κ‖)).add Ia1).add Ia2).sub Ib2).sub Ib1).congr ?_
    filter_upwards [hpt] with z hz
    rw [hz.2]; rfl
  unfold localHeightAtEmbedding
  rw [integral_congr_ae (hpt.mono fun z hz => hz.1)]
  rw [integral_add ?_ (integrable_const _), integral_add ?_ (integrable_const _),
    integral_sub I1 IFX, integral_const, integral_const, d.sphereMean_fubini hFc0 hFcmh, d.sphereMean_substituted_eq_integral]
  · simp only [probReal_univ, one_smul]
  · exact I1.sub IFX
  · exact (I1.sub IFX).add (integrable_const _)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
