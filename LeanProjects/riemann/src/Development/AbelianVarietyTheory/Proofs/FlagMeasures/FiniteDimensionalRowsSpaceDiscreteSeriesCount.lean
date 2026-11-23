import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocDecOfDecGap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureFundamentalDomainLtOfDeepPointBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamilyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.RowsFinMult

theorem finiteDimensional_of_bound {V : Type} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) (N : ℕ)
    (h : ∀ S : Submodule ℂ V, S ≤ W → FiniteDimensional ℂ S → Module.finrank ℂ S ≤ N) :
    FiniteDimensional ℂ W := by
  classical
  by_contra hW
  set b := Module.Basis.ofVectorSpace ℂ W with hb
  haveI : Infinite (Module.Basis.ofVectorSpaceIndex ℂ W) := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hW (Module.Finite.of_basis b)
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq (Module.Basis.ofVectorSpaceIndex ℂ W) (N + 1)
  let u : s → V := fun i => ((b i : W) : V)
  have hli : LinearIndependent ℂ u :=
    (b.linearIndependent.comp _ Subtype.val_injective).map' W.subtype (Submodule.ker_subtype W)
  have hle : Submodule.span ℂ (Set.range u) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  have hbd := h _ hle (FiniteDimensional.span_of_finite ℂ (Set.finite_range u))
  rw [finrank_span_eq_card hli] at hbd
  simp [hs] at hbd

theorem isContRep_sum (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (F : ι → B.I.GA → ℂ) (c : ι → ℂ) (h : ∀ i, IsContRep B (y i) (F i)) :
    IsContRep B (∑ i ∈ s, c i • y i) (fun x => ∑ i ∈ s, c i * F i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · unfold GlobalTheory.Dec.IsContRep
    rw [Finset.sum_empty]
    refine ⟨continuous_const, fun γ _ x => rfl, ?_⟩
    exact Lp.coeFn_zero _ _ _
  · intro a s ha ih
    have e1 : (∑ i ∈ insert a s, c i • y i) = (∑ i ∈ s, c i • y i) + c a • y a := by
      rw [Finset.sum_insert ha, add_comm]
    have e2 : (fun x => ∑ i ∈ insert a s, c i * F i x) =
        (fun x => (∑ i ∈ s, c i * F i x) + c a * F a x) := by
      funext x
      rw [Finset.sum_insert ha, add_comm]
    rw [e1, e2]
    exact (GlobalTheory.ContRepUniq.contRep_unique_linear B).2.1 _ _ _ _ (c a) ih (h a)

theorem vol_lt_top (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (B : RowsAut) (p q : ℕ) (hs : SigIs B p q)
    (hq : q ^ 2 ≤ B.I.n) (hn : 8 ≤ B.I.n) (hrd : 1 ≤ B.I.rd) :
    0 < B.I.muA B.μf B.fund ∧ B.I.muA B.μf B.fund < ⊤ := by
  haveI := B.haar
  haveI := B.sf
  have hpos := (GlobalTheory.CovolRat.covol_eq_inter_fund B.I B.μf B.fund Set.univ B.fund_spec
    MeasurableSet.univ (by simp)).2
  refine ⟨hpos, ?_⟩
  choose c hc0 hc hcu using fun v => GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
  have hf0 : (0 : ℝ) ≤ B.I.f := by positivity
  have hrd1 : (1 : ℝ) ≤ B.I.rd := hrd
  have hx := hV B.I p q hs hq hn (2 * B.I.f * B.I.rd + B.I.rd + 2) (by nlinarith) (by nlinarith)
    (by nlinarith) c B.μf
  first | unfold GlobalTheory.FlagMeas.gaugeVol at hx | unfold gaugeVol at hx | skip
  first | unfold GlobalTheory.FlagMeas.IsGaugeAll at hx | unfold IsGaugeAll at hx | skip
  have hx2 := hx hc
  have hcov := (GlobalTheory.CovolRat.covol_eq_inter_fund B.I B.μf B.fund Set.univ B.fund_spec
    MeasurableSet.univ (by simp)).1
  rw [hcov, Set.univ_inter] at hx2
  have hK := (GlobalTheory.CongIndex.measure_Kset_le B.I B.μf 1 le_rfl).2.2
  have ha : ENNReal.ofReal (∏ v, c v) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Finset.prod_pos fun v _ => hc0 v)).ne'
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.mul_top ha, ENNReal.top_div_of_ne_top hK.ne, top_le_iff] at hx2
  exact ENNReal.ofReal_ne_top hx2

theorem half_le_least (I : AutInst) (hn : 1 ≤ I.n) (h0 : ∀ v, rkR (I.ε v) = 0) (x : I.GA) :
    1 / 2 ≤ least I x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := by
    first
    | exact inferInstance
    | exact ⟨InfinitePlace.mk (Classical.arbitrary _)⟩
  have h1 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
  rw [h0 v] at h1
  have hbot : stepLt I x (1 / 2) = ⊥ := by
    have h2 : Formalism.HN.rkK (stepLt I x (1 / 2)) = 0 := by omega
    unfold Formalism.HN.rkK at h2
    rw [Submodule.finrank_eq_zero] at h2
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ Submodule.span I.E (stepLt I x (1 / 2) : Set (Fin I.n → I.E)) :=
      Submodule.subset_span hy
    rw [h2] at hy'
    simpa using hy'
  exact ((GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn).2.2.mp hbot

theorem bessel (B : RowsAut) (C : ℝ) (t : B.I.GA → ℝ) (w : B.Hs) (hw : ‖w‖ = 1)
    (hC : ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A w) = A w) →
      ∃ f : B.I.GA → ℂ, IsContRep B (A w) f ∧ ∀ x, ‖f x‖ ≤ C * t x * ‖A w‖)
    {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (F : Fin D → B.I.GA → ℂ)
    (hT : ∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R)
    (hk : ∀ i, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i w) = T i w)
    (hiso : ∀ i u, ‖T i u‖ = ‖u‖) (horth : ∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0)
    (hF : ∀ i, IsContRep B (T i w) (F i)) (x : B.I.GA) :
    ∑ i, ‖F i x‖ ^ 2 ≤ (C * t x) ^ 2 := by
  classical
  set c : Fin D → ℂ := fun i => star (F i x) with hc
  set A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund := ∑ i, c i • T i with hA
  have hAw : A w = ∑ i, c i • T i w := by
    rw [hA, ContinuousLinearMap.sum_apply]
    rfl
  have hAmem : A ∈ B.I.HomS B.σs B.μf B.fund B.R :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hT i))
  have hAk : ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A w) = A w := by
    intro k hk'
    rw [hAw, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hk i k hk']
  obtain ⟨f, hf, hfb⟩ := hC A hAmem hAk
  have hsum := isContRep_sum B Finset.univ (fun i => T i w) F c hF
  rw [← hAw] at hsum
  have hfeq := (GlobalTheory.ContRepUniq.contRep_unique_linear B).1 _ _ _ hf hsum
  set S := ∑ i, ‖F i x‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hfxS : f x = (S : ℂ) := by
    rw [hfeq, hSdef]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc]
    first
    | exact Complex.conj_mul' _
    | exact RCLike.conj_mul _
    | simp [Complex.conj_mul']
  have hon : Orthonormal ℂ (fun i => T i w) :=
    ⟨fun i => by simp [hiso, hw], fun i j hij => horth i j hij w w⟩
  have hAn : ‖A w‖ ^ 2 = S := by
    rw [@norm_sq_eq_re_inner ℂ, hAw, hon.inner_sum c c Finset.univ, hSdef]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e1 : (starRingEnd ℂ) (c i) * c i = ((‖F i x‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul, hc]
      simp
    rw [e1]
    first
    | exact RCLike.ofReal_re _
    | exact Complex.ofReal_re _
    | simp only [RCLike.re_to_complex, Complex.ofReal_re]
    | rfl
  have hAn' : ‖A w‖ = Real.sqrt S := by
    rw [← hAn, Real.sqrt_sq (norm_nonneg _)]
  have key : S ≤ C * t x * Real.sqrt S := by
    have h1 := hfb x
    rw [hfxS, Complex.norm_of_nonneg hS0, hAn'] at h1
    exact h1
  have hr := Real.sq_sqrt hS0
  have hr0 := Real.sqrt_nonneg S
  by_cases hS : S = 0
  · rw [hS]
    positivity
  have hrpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr (lt_of_le_of_ne hS0 (Ne.symm hS))
  have hra : Real.sqrt S ≤ C * t x := by nlinarith
  nlinarith

private theorem sum_lintegral_le_lintegral_sum {X : Type} [MeasurableSpace X] (μ : Measure X) {ι : Type}
    (s : Finset ι) (f : ι → X → ENNReal) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    calc ∫⁻ x, f a x ∂μ + ∑ i ∈ s, ∫⁻ x, f i x ∂μ
        ≤ ∫⁻ x, f a x ∂μ + ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by gcongr
      _ ≤ ∫⁻ x, (f a x + ∑ i ∈ s, f i x) ∂μ := le_lintegral_add _ _

theorem card_le_of_pointwise (B : RowsAut) (hfin : B.I.muA B.μf B.fund < ⊤) {D : ℕ}
    (y : Fin D → B.I.L2 B.μf B.fund) (F : Fin D → B.I.GA → ℂ) (hy : ∀ i, ‖y i‖ = 1)
    (hF : ∀ i, IsContRep B (y i) (F i)) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ∑ i, ‖F i x‖ ^ 2 ≤ K) :
    (D : ℝ) ≤ K * (B.I.muA B.μf B.fund).toReal := by
  have hU := GlobalTheory.ContRepUniq.contRep_unique_linear B
  have hone : ∀ i, ∫⁻ x in B.fund, ‖F i x‖ₑ ^ 2 ∂(B.I.muA B.μf) = 1 := by
    intro i
    rw [(hU.2.2.2 _ _ (hF i)).2, hy i]
    simp
  have h1 : (D : ENNReal) ≤ ∫⁻ x in B.fund, ∑ i, ‖F i x‖ₑ ^ 2 ∂(B.I.muA B.μf) := by
    calc (D : ENNReal) = ∑ i : Fin D, ∫⁻ x in B.fund, ‖F i x‖ₑ ^ 2 ∂(B.I.muA B.μf) := by
          simp [hone]
      _ ≤ _ := sum_lintegral_le_lintegral_sum _ _ _
  have h2 : ∫⁻ x in B.fund, ∑ i, ‖F i x‖ₑ ^ 2 ∂(B.I.muA B.μf) ≤
      ENNReal.ofReal K * B.I.muA B.μf B.fund := by
    calc ∫⁻ x in B.fund, ∑ i, ‖F i x‖ₑ ^ 2 ∂(B.I.muA B.μf)
        ≤ ∫⁻ x in B.fund, ENNReal.ofReal K ∂(B.I.muA B.μf) := by
          apply lintegral_mono
          intro x
          calc ∑ i, ‖F i x‖ₑ ^ 2 = ENNReal.ofReal (∑ i, ‖F i x‖ ^ 2) := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hK x)
      _ = ENNReal.ofReal K * B.I.muA B.μf B.fund := by rw [setLIntegral_const]
  have h3 : (D : ENNReal) ≤ ENNReal.ofReal K * B.I.muA B.μf B.fund := h1.trans h2
  have hne : ENNReal.ofReal K * B.I.muA B.μf B.fund ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have h4 := (ENNReal.toReal_le_toReal (by simp) hne).mpr h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at h4
  simpa using h4

private theorem le_mul_div_of_le_mul_div_of_mul_le (S P Q R Dr V e : ℝ) (hV : 0 < V) (hDr : 0 ≤ Dr)
    (h1 : S ≤ P * Dr * Q / R) (h2 : P * Q / R * V ≤ e) : S ≤ Dr * e / V := by
  have h3 : P * Q / R ≤ e / V := by
    rw [le_div_iff₀ hV]
    exact h2
  calc S ≤ P * Dr * Q / R := h1
    _ = (P * Q / R) * Dr := by ring
    _ ≤ (e / V) * Dr := mul_le_mul_of_nonneg_right h3 hDr
    _ = Dr * e / V := by ring

theorem rows_finiteDimensional : GlobalTheory.DSId.DecGap → GlobalTheory.FlagMeas.AbsoluteVolume → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) := by
  intro hD hV B Cg n₀ d p q b hn₀ hH
  have hB : IsDSData B d := hH.1
  have hs : SigIs B p q := hH.2.1
  have hqn : q ^ 2 ≤ B.I.n := hH.2.2.2.1
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hH.2.2.1
  have hg : 1 ≤ B.g := hH.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hrd, hf1, -, -, -, hrk, -, -, -, hts, -, h, -, hgap, hbig40, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hH
  have hK := GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hH
  have h120' : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    intro v
    rw [hrk v]
    exact h120
  have hLoc := GlobalTheory.Dec.locDec_of_decGap hD B d h hB hgap h120'
  have hE := GlobalTheory.T.idempotent_intertwiner_images_cuspidal_of_level B d h hB hK hg h120' hLoc hbig40
  obtain ⟨hvpos, hvtop⟩ := vol_lt_top hV B p q hs hqn hn8 hrd
  obtain ⟨C, hC⟩ := GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf B d hB hK (by omega) hg
  have hw1 : ‖B.tens B.w‖ = 1 := by
    have e' : ∀ v, ⟪B.w v, B.w v⟫_ℂ = 1 := fun v => by
      rw [inner_self_eq_norm_sq_to_K, (hB v).2.2.1.1]
      simp
    have e3 : ‖B.tens B.w‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, B.tens_spec.1, Finset.prod_congr rfl (fun v _ => e' v),
        Finset.prod_const_one]
      simp
    have e4 := norm_nonneg (B.tens B.w)
    nlinarith
  choose c hc0 hc hcu using fun v => GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
  have hVpos : 0 < (B.I.muA B.μf B.fund).toReal := ENNReal.toReal_pos hvpos.ne' hvtop.ne
  set V := (B.I.muA B.μf B.fund).toReal with hVdef
  set m : ℝ := min (1 / 2) (tauStar B q b) with hmdef
  have hm : 0 < m := lt_min (by norm_num) hts
  set M : ℝ := m⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) with hMdef
  set e : ℝ := Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) with hedef
  have he : e ≤ 1 / 2 := by
    have hy1 : (1 : ℝ) ≤ (B.I.n : ℝ) ^ 2 * B.I.f := by
      have a1 : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn8
      have a2 : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf1
      nlinarith
    have a3 := Real.add_one_le_exp ((B.I.n : ℝ) ^ 2 * B.I.f)
    have a4 : e * Real.exp ((B.I.n : ℝ) ^ 2 * B.I.f) = 1 := by
      rw [hedef, ← Real.exp_add]
      simp
    have a5 := Real.exp_pos (-((B.I.n : ℝ) ^ 2 * B.I.f))
    rw [← hedef] at a5
    nlinarith
  refine finiteDimensional_of_bound _ (Nat.ceil (2 * (C ^ 2 * M ^ 2) * V)) (fun S hS hSfd => ?_)
  have hSH : S ≤ B.I.HomS B.σs B.μf B.fund B.R := fun A hA => (hE A (hS hA)).1
  obtain ⟨T, hTS, hiso, horth⟩ :=
    GlobalTheory.IntertwinerFrame.exists_orthonormal_frame_of_le B d hB S hSH hSfd
  have hTH : ∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R := fun i => hSH (hTS i)
  have hTk : ∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u :=
    fun i u => ((hE _ (hS (hTS i))).2 u).2
  have hTc : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u)) :=
    fun i u => ((hE _ (hS (hTS i))).2 u).1
  choose Fr hFr using fun i => GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType B d hB hK hg (T i) (hTH i) (fun u k hk => hTk i u k hk)
  have hmem : B.tens B.w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B 0 := by
    apply Submodule.subset_span
    refine ⟨[], B.w, by simp, fun v => (hB v).2.2.1.2, ?_⟩
    first
    | rfl
    | simp [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.wordAct]
  have hG : ∀ i, IsContRep B (T i (B.tens B.w)) (Fr i (B.tens B.w)) :=
    fun i => (hFr i 0 _ hmem).1
  have hy : ∀ i, ‖T i (B.tens B.w)‖ = 1 := fun i => by rw [hiso, hw1]
  have hD0 : (0 : ℝ) ≤ (Module.finrank ℂ S) := Nat.cast_nonneg _
  have hpt : ∀ x, ∑ i, ‖Fr i (B.tens B.w) x‖ ^ 2 ≤ (Module.finrank ℂ S) * e / V + C ^ 2 * M ^ 2 := by
    intro x
    have hfirst : 0 ≤ ((Module.finrank ℂ S) : ℝ) * e / V := by positivity
    have hsecond : 0 ≤ C ^ 2 * M ^ 2 := by positivity
    by_cases hx : 1 ≤ q ∧ least B.I x < tauStar B q b
    · have h1 := GlobalTheory.T.deepPoint_bound_cuspidalIsometricIntertwinerFamily B Cg n₀ d p q b c x (Module.finrank ℂ S) T Fr hn₀ hx.1 hH hc hx.2 hFr hiso hTc
      have h2 := (GlobalTheory.T.measure_fundamentalDomain_lt_of_deepPoint_bound hV B Cg n₀ d p q b c x hn₀ hx.1 hH hc hx.2).2
      have hvv : ‖GlobalTheory.Deep.vv B Fr (B.tens B.w) x‖ ^ 2 = ∑ i, ‖Fr i (B.tens B.w) x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [GlobalTheory.Deep.vv]
      rw [hvv] at h1
      have h3 := le_mul_div_of_le_mul_div_of_mul_le _ _ _ _ _ _ _ hVpos hD0 h1 h2
      linarith
    · have htau : m ≤ tau1 B.I x := by
        show m ≤ min (1 / 2) (least B.I x)
        rcases Nat.eq_zero_or_pos q with hq0 | hq1
        · have hl := half_le_least B.I (by omega) (fun v => by rw [hrk v, hq0]) x
          rw [min_eq_left hl]
          exact min_le_left _ _
        · have hle : tauStar B q b ≤ least B.I x := by
            by_contra hlt
            exact hx ⟨hq1, not_le.mp hlt⟩
          exact min_le_min le_rfl hle
      have hb := bessel B C (fun x => (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) (B.tens B.w) hw1 hC
        T (fun i => Fr i (B.tens B.w)) hTH (fun i => hTk i _) hiso horth hG x
      have ht0 : 0 ≤ (tau1 B.I x)⁻¹ := inv_nonneg.mpr (le_trans hm.le htau)
      have ht1 : (tau1 B.I x)⁻¹ ≤ m⁻¹ := inv_anti₀ hm htau
      have ht2 : (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) ≤ M := pow_le_pow_left₀ ht0 ht1 _
      have ht3 : 0 ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := pow_nonneg ht0 _
      have h4 : (C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) ^ 2 ≤ C ^ 2 * M ^ 2 := by
        rw [mul_pow]
        gcongr
      linarith
  have hK0 : 0 ≤ ((Module.finrank ℂ S) : ℝ) * e / V + C ^ 2 * M ^ 2 := by positivity
  have hcard := card_le_of_pointwise B hvtop (fun i => T i (B.tens B.w)) (fun i => Fr i (B.tens B.w))
    hy hG _ hK0 hpt
  rw [← hVdef, add_mul, div_mul_cancel₀ _ hVpos.ne'] at hcard
  have hDB : ((Module.finrank ℂ S) : ℝ) ≤ 2 * (C ^ 2 * M ^ 2) * V := by nlinarith
  have hfin : ((Module.finrank ℂ S) : ℝ) ≤ (Nat.ceil (2 * (C ^ 2 * M ^ 2) * V) : ℕ) := le_trans hDB (Nat.le_ceil _)
  exact_mod_cast hfin

end GlobalTheory.RowsFinMult
