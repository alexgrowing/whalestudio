import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem blockSphereProb_isProbabilityMeasure {B n : ℕ} (hn : 0 < n) :
    MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.blockSphereProb B n) := by
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  haveI : MeasureTheory.IsProbabilityMeasure (ReciprocityTheory.MultiplicativeHeights.sphereProb n) := by
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb
    have hne : ∃ x : EuclideanSpace ℂ (Fin n), x ≠ 0 :=
      ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr hne
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
      exact_mod_cast hdim.ne'
    · rw [MeasureTheory.Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (MeasureTheory.measure_ball_lt_top).ne
  infer_instance

theorem height_const_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : K) :
    ReciprocityTheory.MultiplicativeHeights.h0 (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  unfold ReciprocityTheory.MultiplicativeHeights.h0
  haveI := blockSphereProb_isProbabilityMeasure (B := B) hn
  have hmean : ∀ σ : K →+* ℂ,
      ReciprocityTheory.MultiplicativeHeights.blockSphereMean B n (MvPolynomial.map σ (MvPolynomial.C a)) = Real.log ‖σ a‖ := by
    intro σ
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  have hgauss : ∀ w : FinitePlace K,
      ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = w a := by
    intro w
    unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
    by_cases ha : a = 0
    · simp [ha]
    · rw [MvPolynomial.support_C, if_neg ha, Finset.sup_singleton, MvPolynomial.coeff_C, if_pos rfl,
        Real.coe_toNNReal (w a) (by exact w.1.nonneg a)]
  simp_rw [hgauss, hmean]
  by_cases ha : a = 0
  · simp [ha]
  rw [div_eq_zero_iff]
  left
  have hfin : (Function.mulSupport fun w : FinitePlace K => w a).Finite :=
    NumberField.FinitePlace.mulSupport_finite ha
  have hsub : (Function.support fun w : FinitePlace K => Real.log (w a)) ⊆ hfin.toFinset := by
    intro w hw
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    show Real.log (w a) = 0
    rw [h1, Real.log_one]
  rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun w _ => w.1.ne_zero ha),
    ← finprod_eq_prod_of_mulSupport_subset _ (by rw [Set.Finite.coe_toFinset]),
    NumberField.FinitePlace.prod_eq_inv_abs_norm ha,
    ← Real.log_prod (fun σ _ => by simpa using ha), ← norm_prod]
  have hN : ∏ σ : K →+* ℂ, σ a = ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ a) (fun σ => σ a) (fun σ => rfl),
      ← Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    simp
  rw [hN]
  push_cast
  rw [Real.log_inv]
  simp

theorem not_injective_of_trdeg_lt {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {σ τ : Type}
    [Fintype σ] [Fintype τ] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ Ω) (n : ℕ)
    (hn : Algebra.trdeg K Ω = n) (hlt : n + Fintype.card τ < Fintype.card σ) :
    ¬ Function.Injective φ := by
  intro hinj
  have hai : AlgebraicIndependent K (φ ∘ fun i : σ => (MvPolynomial.X i : MvPolynomial σ K)) :=
    (MvPolynomial.algebraicIndependent_X σ K).map' hinj
  have hle := hai.cardinalMk_le_trdeg
  have h1 : Algebra.trdeg Ω (MvPolynomial τ Ω) = Cardinal.mk τ := by
    first
    | simpa using (MvPolynomial.trdeg_of_isDomain (R := Ω) (σ := τ))
    | simpa using (MvPolynomial.trdeg_of_isDomain Ω τ)
    | simpa using (MvPolynomial.trdeg (R := Ω) (σ := τ))
    | simpa using (Algebra.trdeg_mvPolynomial (R := Ω) (σ := τ))
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).lift_cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.isTranscendenceBasis_X τ Ω).cardinalMk_eq_trdeg).symm
    | simpa using ((MvPolynomial.algebraicIndependent_X τ Ω).isTranscendenceBasis_iff_isAlgebraic.mpr
        inferInstance).lift_cardinalMk_eq_trdeg.symm
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial τ Ω) =
      Algebra.trdeg K (MvPolynomial τ Ω) := by
    first
    | exact trdeg_add_eq K Ω
    | exact Algebra.trdeg_add_eq K Ω
  rw [← h2, hn, h1, Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
  have hc : Fintype.card σ ≤ n + Fintype.card τ := by exact_mod_cast hle
  omega

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_one_prime_eq_span_gen (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) :
    p = Ideal.span {d.gen p} := by
  haveI := hp.1
  have hpr : p.IsPrincipal := by
    obtain ⟨g, _, hg⟩ := ValUFD.heightOne_principal p hp.2
    exact ⟨⟨g, hg⟩⟩
  unfold Data.gen
  rw [dif_pos hpr]
  exact (Ideal.span_singleton_generator p).symm

theorem fZ_factor_positive_places (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ (κ : K) (T : Finset (Ideal (KTp K d.D d.N))) (e : Ideal (KTp K d.D d.N) → ℕ),
      κ ≠ 0 ∧ (↑T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne ∧
      F = MvPolynomial.C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, 0 < e p → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hOfin, hrest⟩ := d.norm_by_places hd h c
  obtain ⟨hP0fin, κ, hκ, hnorm⟩ := hrest (d.rationalBaseRow c) hy
  obtain ⟨E, hE⟩ : ∃ E : Ideal (KTp K d.D d.N) → ℤ, ∀ p, E p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Ideal (KTp K d.D d.N) → ℤ, ∀ p, Nn p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p \ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  simp only [← hE] at hnorm

  have htriv : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := by
    rintro p w ⟨hO, hG⟩ a ha
    by_contra hne
    exact hG ⟨hO, a, ha, hne⟩
  have hwy : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → 0 ≤ w (d.rationalBaseRow c) :=
    fun p w hw => d.lineRatio_val_nonneg c p w hw.1 (htriv p w hw)
  have hNn0 : ∀ p, 0 ≤ Nn p := by
    intro p
    rw [hNn]
    exact finsum_nonneg fun w => finsum_nonneg fun hw =>
      mul_nonneg (Nat.cast_nonneg _) (untopD_nonneg (hwy p w hw))

  have hsplit : ∀ p ∈ d.HtOne, E p + d.nPMM h c (d.w (d.jc c) c) p = Nn p := by
    intro p hp
    have hGsub : d.GoodP c p ⊆ d.OverP c p := fun w hw => hw.1
    have hGfin : (d.GoodP c p).Finite := (hOfin p hp).subset hGsub
    have hgood : d.nPMM h c (d.w (d.jc c) c) p =
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) := by
      unfold Data.nPMM
      refine finsum_mem_congr rfl fun w hw => ?_
      have h1 := d.good_valuation_balance hd h c p hp w hw
      rw [show d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = -WithTop.untopD 0 (w (d.rationalBaseRow c)) by linarith]
      ring
    have hsum : (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) +
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) = 0 := by
      rw [← finsum_mem_add_distrib' (hGfin.inter_of_left _) (hGfin.inter_of_left _)]
      simp
    have hO := finsum_mem_union
      (f := fun w => (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)))
      (Set.disjoint_sdiff_right : Disjoint (d.GoodP c p) (d.OverP c p \ d.GoodP c p)) hGfin
      ((hOfin p hp).subset Set.diff_subset)
    rw [Set.union_diff_cancel hGsub] at hO
    beta_reduce at hO
    rw [hE, hNn, hgood, hO]
    linarith

  have hout : ∀ p ∈ d.HtOne, p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} →
      E p = 0 ∧ Nn p = 0 := by
    intro p hp hpP
    have hz : ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
      intro w hw
      by_contra hne
      exact hpP ⟨hp, w, hw, hne⟩
    constructor
    · rw [hE]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw]
      simp
    · rw [hNn]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw.1]
      simp
  have hTS : (↑hP0fin.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro p hp
    rw [Set.Finite.coe_toFinset] at hp
    exact hp.1
  have hnotT : ∀ p ∈ d.HtOne, p ∉ hP0fin.toFinset →
      p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} := by
    intro p _ hpT hpP
    exact hpT ((Set.Finite.mem_toFinset hP0fin).mpr hpP)
  have hgen0 : ∀ p ∈ d.HtOne, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)
  have hprodE : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p) =
      ∏ p ∈ hP0fin.toFinset, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p = 1
    rw [(hout p hpS (hnotT p hpS hpT)).1, zpow_zero]
  have hprodM : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p) =
      ∏ p ∈ hP0fin.toFinset,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p = 1
    have h1 := hout p hpS (hnotT p hpS hpT)
    have h2 := hsplit p hpS
    rw [show d.nPMM h c (d.w (d.jc c) c) p = 0 by linarith [h1.1, h1.2], zpow_zero]
  have hF' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.C κ * ∏ p ∈ hP0fin.toFinset, d.gen p ^ (Nn p).toNat) := by
    rw [hF]
    simp only [Data.fZ]
    rw [hnorm, hprodE, hprodM, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod]
    rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) κ, MvPolynomial.algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpS := hTS (Finset.mem_coe.mpr hp)
    rw [← zpow_add₀ (hgen0 p hpS), hsplit p hpS, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (hNn0 p)]
  refine ⟨κ, hP0fin.toFinset, fun p => (Nn p).toNat, hκ, hTS,
    IsFractionRing.injective _ _ hF', ?_⟩
  intro p hpT hpos
  by_contra hne
  push_neg at hne
  have hz : Nn p = 0 := by
    rw [hNn]
    refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
    have h0 : w (d.rationalBaseRow c) = 0 := le_antisymm (hne w hw.1 (htriv p w hw)) (hwy p w hw)
    rw [h0]
    simp
  simp [hz] at hpos

end Data

end ReciprocityTheory.ChartRestriction.G.T0
