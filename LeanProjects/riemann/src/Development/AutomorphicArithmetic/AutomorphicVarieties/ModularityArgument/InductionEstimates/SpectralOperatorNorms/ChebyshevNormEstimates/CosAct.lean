import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinAct
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem coset_pre {G : Type*} [Group G] (U : Subgroup G) (c : G ⧸ U) :
    (QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c} = (fun g => c.out⁻¹ * g) ⁻¹' (U : Set G) := by
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  exact eq_comm

private theorem coset_fin {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) (h : G) :
    {c : G ⧸ U | ∃ k ∈ U, c = QuotientGroup.mk (k * h)}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology ho
  have h1 : IsCompact ((fun k : G => (QuotientGroup.mk (k * h) : G ⧸ U)) '' (U : Set G)) :=
    hc.image (QuotientGroup.continuous_mk.comp (continuous_mul_const h))
  refine h1.finite_of_discrete.subset ?_
  rintro c ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩

private theorem coset_cpt {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (U : Subgroup G)
    (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) (c : G ⧸ U) :
    IsClopen ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c}) ∧ IsCompact ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c}) := by
  rw [coset_pre]
  refine ⟨⟨(U.isClosed_of_isOpen ho).preimage (continuous_const_mul _), ho.preimage (continuous_const_mul _)⟩, ?_⟩
  exact (Homeomorph.mulLeft c.out⁻¹).isCompact_preimage.2 hc

private theorem coset_fun {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m] (U : Subgroup G)
    (ho : IsOpen (U : Set G)) (hc : IsCompact (U : Set G)) (t : Finset (G ⧸ U)) (a : ℂ) :
    ∃ e : CompactlySupportedContinuousMap G ℂ,
      (∀ g, e g = ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' (t : Set (G ⧸ U))).indicator (fun _ => a) g) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : G → E), Continuous F →
        ∫ g, e g • F g ∂m = ∑ c ∈ t, ∫ g, (U : Set G).indicator (fun _ => a) g • F (c.out * g) ∂m := by
  classical
  have hT : (QuotientGroup.mk : G → G ⧸ U) ⁻¹' (t : Set (G ⧸ U)) = ⋃ c ∈ t, (QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c} := by
    ext g
    simp
  have hcl : IsClopen ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' (t : Set (G ⧸ U))) := by
    rw [hT]
    exact isClopen_biUnion_finset fun c _ => (coset_cpt U ho hc c).1
  have hcp : IsCompact ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' (t : Set (G ⧸ U))) := by
    rw [hT]
    exact t.isCompact_biUnion fun c _ => (coset_cpt U ho hc c).2
  refine ⟨⟨⟨_, hcl.continuous_indicator (continuous_const (y := a))⟩,
    HasCompactSupport.intro hcp fun x hx => Set.indicator_of_notMem hx (fun _ => a)⟩, fun _ => rfl, ?_⟩
  intro E _ _ F hF
  have h1 : ∀ g, ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' (t : Set (G ⧸ U))).indicator (fun _ => a) g • F g =
      ∑ c ∈ t, ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c}).indicator (fun _ => a) g • F g := fun g => by
    rw [← Finset.sum_smul]
    congr 1
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
    rw [Finset.sum_ite_eq]
  have h2 : ∀ c ∈ t, Integrable (fun g => ((QuotientGroup.mk : G → G ⧸ U) ⁻¹' {c}).indicator (fun _ => a) g • F g) m :=
    fun c _ => (((coset_cpt U ho hc c).1.continuous_indicator continuous_const).smul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (coset_cpt U ho hc c).2 fun x hx => by
        rw [Pi.smul_apply', Set.indicator_of_notMem hx, zero_smul])
  refine (integral_congr_ae (Eventually.of_forall h1)).trans ?_
  rw [integral_finset_sum _ h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← integral_mul_left_eq_self _ c.out, coset_pre]
  congr 1
  funext g
  simp only [Set.indicator_apply, Set.mem_preimage, inv_mul_cancel_left]

private theorem fin_facts {K : Type} [Field K] [NumberField K] {n : ℕ} {k : AdelicGLn.FiniteAdelicGL K n}
    (hk : k ∈ AdelicGLn.integralFiniteGL K n) :
    ((MultiplicityOne.finProj K n k : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n k ∧
    finEmb K n k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) ∧
    AdelicGLn.prodEquiv K n (finEmb K n k) = (1, k) := by
  refine ⟨?_, finEmb_mem_maxCompact hk, ?_⟩
  · rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hk))]
  · exact (AdelicGLn.prodEquiv K n).apply_symm_apply _

private theorem level_open {K : Type} [Field K] [NumberField K] {n : ℕ} {D : TypeDat K n}
    {Kf : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K n) :
    IsOpen (Kf : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  obtain ⟨O, hO, hU⟩ := D.isOpen
  have : (Kf : Set (AdelicGLn.FiniteAdelicGL K n)) = (AdelicGLn.integralFiniteGL K n : Set _) ∩ finEmb K n ⁻¹' O := by
    ext k
    constructor
    · intro hk
      obtain ⟨h1, h2, h3⟩ := fin_facts (hle hk)
      have := (hL.1 (MultiplicityOne.finProj K n k) (by rw [h1, h3])).2 (by rw [h1, h3]; exact hk)
      rw [hU, h1] at this
      exact ⟨hle hk, this.1⟩
    · rintro ⟨hk, hk'⟩
      obtain ⟨h1, h2, h3⟩ := fin_facts hk
      have := (hL.1 (MultiplicityOne.finProj K n k) (by rw [h1, h3])).1 (by rw [hU, h1]; exact ⟨hk', h2⟩)
      rw [h1, h3] at this
      exact this
  rw [this]
  exact (AdelicGLn.isOpen_integralFiniteGL K n).inter (hO.preimage continuous_finEmb)

private theorem fix_inv {K : Type} [Field K] [NumberField K] {n : ℕ} {D : TypeDat K n}
    {Kf : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K n)
    {f : G1 K n → ℂ} (hf : D.Fix f) {k : AdelicGLn.FiniteAdelicGL K n} (hk : k ∈ Kf) (g : G1 K n) :
    f (g * MultiplicityOne.finProj K n k) = f g := by
  obtain ⟨h1, h2, h3⟩ := fin_facts (hle hk)
  have h4 : (AdelicGLn.prodEquiv K n (MultiplicityOne.finProj K n k : G1 K n)).1 = 1 := by rw [h1, h3]
  have hU : MultiplicityOne.finProj K n k ∈ D.U := (hL.1 _ h4).2 (by rw [h1, h3]; exact hk)
  rw [← hf g, ← hf (g * _), ← (D.inv _ hU).integral_comp (measurableEmbedding_mulLeft _) fun y => D.e y * f (g * y)]
  refine integral_congr_ae ?_
  filter_upwards [D.supp] with y hy
  rw [hL.2.2 _ hU h4 y hy, mul_assoc]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cosAct :
    ForAllC fun K _ _ μ _ _ _ _ _ D d _ A A' => ∀ (Kf : Subgroup (AdelicGLn.FiniteAdelicGL K (2 + 2))), D.Level Kf → Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2) →
      ∀ (h : AdelicGLn.FiniteAdelicGL K (2 + 2)) (Y : L2 μ →L[ℂ] L2 μ),
      Y = (∑ᶠ c ∈ {c : AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ Kf | ∃ k ∈ Kf, c = QuotientGroup.mk (k * h)}, rhoF μ c.out) ∘L prj (fixF μ Kf) →
      (∃ s, Act A.J Y s ∧ ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)), flat z (A.sec (s z v)) x =
        ∑ᶠ c ∈ {c : AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ Kf | ∃ k ∈ Kf, c = QuotientGroup.mk (k * h)},
          flat z (A.sec v) (x * MultiplicityOne.finProj K (2 + 2) c.out)) ∧ ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → Y ∘L P = P ∘L Y := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' Kf hL hle h Y hY
  have ho := level_open hL hle
  have hc : IsCompact (Kf : Set (AdelicGLn.FiniteAdelicGL K (2 + 2))) :=
    (AdelicGLn.isCompact_integralFiniteGL K (2 + 2)).of_isClosed_subset (Kf.isClosed_of_isOpen ho) hle
  have hfin := coset_fin Kf ho hc h
  let m : Measure (AdelicGLn.FiniteAdelicGL K (2 + 2)) := Measure.haar
  have hpos : (m.real Kf : ℝ) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(ho.measure_pos m ⟨1, Kf.one_mem⟩).ne', hc.measure_lt_top.ne⟩
  obtain ⟨e, he, hint⟩ := coset_fun m Kf ho hc hfin.toFinset ((m.real Kf : ℝ) : ℂ)⁻¹
  obtain ⟨e₀, he₀, hO₀⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K (2 + 2) μ m Kf ho hc
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K (2 + 2) μ Kf
  have hO : ∀ (e : TF K (2 + 2)) v, Ofin μ m e v = ∫ h, e h • rhoF μ h v ∂m := fun e v => by
    unfold Ofin
    rw [UnitaryRep.integrated_ccToL1_apply]
    rfl
  have hcont : ∀ v, Continuous fun h => rhoF μ h v := fun v =>
    ((rightRegularRep (rationalGLOne K (2 + 2)) μ).continuous_orbit v).comp MultiplicityOne.continuous_finProj
  have hYe : Y = Ofin μ m e := by
    rw [hY, finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hO, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
    refine Eq.trans ?_ (hint _ _ (hcont v)).symm
    refine Finset.sum_congr rfl fun c _ => ?_
    have hi : Integrable (fun h => e₀ h • rhoF μ h v) m :=
      (e₀.continuous.smul (hcont v)).integrable_of_hasCompactSupport e₀.hasCompactSupport.smul_right
    rw [← hO₀, hO, ← ContinuousLinearMap.integral_comp_comm _ hi]
    congr 1
    funext g
    rw [map_smul, he₀, hmul, ContinuousLinearMap.comp_apply]
  have hmem : ∀ g, g ∈ (QuotientGroup.mk : _ → AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ Kf) ⁻¹' (hfin.toFinset : Set _) ↔
      ∃ k ∈ Kf, g⁻¹ * (k * h) ∈ Kf := fun g => by
    simp only [Set.mem_preimage, Set.Finite.coe_toFinset, Set.mem_setOf_eq, QuotientGroup.eq]
  have hinv : ∀ k ∈ Kf, ∀ g, e (k * g) = e g ∧ e (g * k) = e g := fun k hk g => by
    classical
    simp only [he, Set.indicator_apply, hmem]
    refine ⟨if_congr ⟨?_, ?_⟩ rfl rfl, if_congr ⟨?_, ?_⟩ rfl rfl⟩
    · rintro ⟨k', hk', h'⟩
      exact ⟨k⁻¹ * k', Kf.mul_mem (Kf.inv_mem hk) hk', by simpa only [mul_inv_rev, mul_assoc] using h'⟩
    · rintro ⟨k', hk', h'⟩
      exact ⟨k * k', Kf.mul_mem hk hk', by simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h'⟩
    · rintro ⟨k', hk', h'⟩
      exact ⟨k', hk', by simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using Kf.mul_mem hk h'⟩
    · rintro ⟨k', hk', h'⟩
      exact ⟨k', hk', by simpa only [mul_inv_rev, mul_assoc] using Kf.mul_mem (Kf.inv_mem hk) h'⟩
  obtain ⟨⟨s, hs, hsz⟩, hP⟩ := finAct K μ μ₂ τ₁ τ₂ hp D d d' A A' Kf hL hle m e hinv
  rw [hYe]
  refine ⟨⟨s, hs, fun z v x => ?_⟩, hP⟩
  obtain ⟨hsec, hfix⟩ := (A.onto (A.sec v)).1 ⟨v, rfl⟩
  obtain ⟨-, hK, -, hH, -⟩ := hpSpec (K := K)
  have hfl : Continuous (flat z (A.sec v)) :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hH))).mul hsec.cont
  have hr : ∀ k ∈ Kf, ∀ y, flat z (A.sec v) (y * MultiplicityOne.finProj K (2 + 2) k) = flat z (A.sec v) y := fun k hk y => by
    obtain ⟨h1, h2, -⟩ := fin_facts (hle hk)
    have h3 : MultiplicityOne.finProj K (2 + 2) k ∈ KG K (2 + 2) := by
      show ((MultiplicityOne.finProj K (2 + 2) k : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
      rw [h1]
      exact h2
    unfold flat
    rw [fix_inv hL hle hfix hk, show HP 2 2 (y * MultiplicityOne.finProj K (2 + 2) k) = HP 2 2 y from (hK _ h3).2 y]
  rw [← hsz, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (hint ℂ (fun g => flat z (A.sec v) (x * MultiplicityOne.finProj K (2 + 2) g))
    (hfl.comp (continuous_const.mul MultiplicityOne.continuous_finProj))).trans (Finset.sum_congr rfl fun c _ => ?_)
  have h5 : ∀ g, (Kf : Set (AdelicGLn.FiniteAdelicGL K (2 + 2))).indicator (fun _ => ((m.real Kf : ℝ) : ℂ)⁻¹) g •
      flat z (A.sec v) (x * MultiplicityOne.finProj K (2 + 2) (c.out * g)) =
      (Kf : Set (AdelicGLn.FiniteAdelicGL K (2 + 2))).indicator (fun _ => ((m.real Kf : ℝ) : ℂ)⁻¹) g •
      flat z (A.sec v) (x * MultiplicityOne.finProj K (2 + 2) c.out) := fun g => by
    by_cases hg : g ∈ Kf
    · rw [map_mul, ← mul_assoc, hr g hg]
    · rw [Set.indicator_of_notMem (show g ∉ (Kf : Set _) from hg), zero_smul, zero_smul]
  simp only [h5]
  rw [integral_smul_const, integral_indicator_const _ ho.measurableSet, Complex.real_smul,
    mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
