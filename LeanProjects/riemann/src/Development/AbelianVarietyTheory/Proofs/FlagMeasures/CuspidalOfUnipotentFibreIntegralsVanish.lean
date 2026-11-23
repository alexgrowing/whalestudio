import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaDiscreteSeriesTestGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRaStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CuspCore

theorem isHaarSub_map_emb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : IsHaarSub (N : Set H) ν) :
    IsClosed ((N.map ι : Subgroup G) : Set G) ∧ IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  rw [Subgroup.coe_map]
  unfold GlobalTheory.Dec.IsHaarSub at hν ⊢
  obtain ⟨h0, hfin, hcon, hinv⟩ := hν
  refine ⟨hι.isClosedMap _ hN, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h0
    have h2 := hme.map_apply ν Set.univ
    rw [h, Set.preimage_univ] at h2
    rw [← Measure.measure_univ_eq_zero]
    simpa using h2.symm
  · have := hfin
    refine ⟨fun K hK => ?_⟩
    rw [hme.map_apply]
    exact (hι.isCompact_preimage hK).measure_lt_top
  · rw [hme.map_apply, Set.preimage_compl, hι.injective.preimage_image]
    exact hcon
  · rintro _ ⟨n, hn, rfl⟩
    rw [Measure.map_map (measurable_const_mul (ι n)) hme.measurable]
    have hcomp : (fun y => ι n * y) ∘ ι = ι ∘ (fun y => n * y) := by
      funext y
      simp only [Function.comp_apply, map_mul]
    rw [hcomp, ← Measure.map_map hme.measurable (measurable_const_mul n), hinv n hn]

theorem constTerm_repro {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [IsFiniteMeasure ν] (f φ : G → ℂ) (hf : Continuous f) (hφ : Measurable φ) (x : G)
    (Φ : G → ℝ) (hΦ : Integrable Φ μ) (hb : ∀ᵐ m ∂ν, ∀ g, ‖φ g * f (m * x * g)‖ ≤ Φ g)
    (hr : ∀ z, f z = ∫ g, φ g * f (z * g) ∂μ) :
    Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ ∧
      ∫ m, f (m * x) ∂ν = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ := by
  have hKm : AEStronglyMeasurable (fun p : G × G => φ p.2 * f (p.1 * x * p.2)) (ν.prod μ) := by
    have h1 : Continuous fun p : G × G => f (p.1 * x * p.2) :=
      hf.comp ((continuous_fst.mul continuous_const).mul continuous_snd)
    exact ((hφ.comp measurable_snd).mul h1.measurable).aestronglyMeasurable
  have hKi : Integrable (fun p : G × G => φ p.2 * f (p.1 * x * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hKm]
    constructor
    · filter_upwards [hb] with m hm
      have hc : Continuous fun g : G => f (m * x * g) := hf.comp (continuous_const_mul (m * x))
      exact Integrable.mono' hΦ (hφ.mul hc.measurable).aestronglyMeasurable (ae_of_all _ hm)
    · refine Integrable.mono' (integrable_const (∫ g, Φ g ∂μ)) hKm.norm.integral_prod_right' ?_
      filter_upwards [hb] with m hm
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hΦ (ae_of_all _ hm)
  have hswap := integral_integral_swap (f := fun m g => φ g * f (m * x * g)) hKi
  have hF : ∀ g, ∫ m, φ g * f (m * x * g) ∂ν =
      (∫ m, f (m * (x * g)) ∂ν) * φ (x⁻¹ * (x * g)) := by
    intro g
    rw [inv_mul_cancel_left, integral_const_mul, mul_comm (φ g)]
    simp only [mul_assoc]
  have hI1 : Integrable (fun g => (∫ m, f (m * (x * g)) ∂ν) * φ (x⁻¹ * (x * g))) μ :=
    hKi.integral_prod_right.congr (ae_of_all _ fun g => hF g)
  have hI : Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ := by
    have h2 := hI1.comp_mul_left x⁻¹
    simpa only [mul_inv_cancel_left] using h2
  refine ⟨hI, ?_⟩
  calc ∫ m, f (m * x) ∂ν = ∫ m, ∫ g, φ g * f (m * x * g) ∂μ ∂ν := by
        congr 1
        funext m
        exact hr (m * x)
    _ = ∫ g, ∫ m, φ g * f (m * x * g) ∂ν ∂μ := hswap
    _ = ∫ g, (∫ m, f (m * (x * g)) ∂ν) * φ (x⁻¹ * (x * g)) ∂μ := by
        congr 1
        funext g
        exact hF g
    _ = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ :=
        integral_mul_left_eq_self (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) x

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) : Continuous (phe B d) := by
  have hcoef : ∀ v, Continuous (fun g : B.I.Ginf => ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ) := by
    intro v
    obtain ⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩ := hd v
    have hu : Continuous (fun g : UJ (B.I.ε v) => uMat g) :=
      Units.continuous_val.comp continuous_subtype_val
    have hin : ∀ g : UJ (B.I.ε v), uMat g ∈ UJset (B.I.ε v) := fun g => g.2
    have h1 : Continuous (fun g : UJ (B.I.ε v) => B.σ v (uMat g) (B.w v)) :=
      (hcont (B.w v)).comp_continuous hu hin
    exact continuous_const.inner (h1.comp (continuous_apply v))
  obtain ⟨hlc, -⟩ := B.e_adm
  have hph : Continuous (ph B d) := by
    unfold GlobalTheory.Count.ph
    exact continuous_const.mul ((continuous_finsetProd _ fun v _ => hcoef v).star)
  unfold GlobalTheory.Count.phe
  exact (hph.comp continuous_fst).mul (hlc.continuous.comp continuous_snd)

theorem one_le_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) : 1 ≤ I.n := by
  obtain ⟨hne, -⟩ := hW
  by_contra hlt
  apply hne
  rw [Submodule.eq_bot_iff]
  intro x _
  funext i
  exact absurd i.isLt (by omega)

open Classical in

noncomputable def incl (I : AutInst) (v : InfinitePlace I.F) : UJ (I.ε v) →* I.GA :=
  (MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun v => UJ (I.ε v)) v)

theorem isClosedEmbedding_incl (I : AutInst) (v : InfinitePlace I.F) : Topology.IsClosedEmbedding (incl I v) := by
  classical
  obtain ⟨hT2, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have := hT2
  have hform : ∀ m : UJ (I.ε v), incl I v m = (Pi.mulSingle v m, 1) := fun m => rfl
  have hc : Continuous (incl I v) := by
    have h1 : (incl I v : UJ (I.ε v) → I.GA) = fun m : UJ (I.ε v) => ((Pi.mulSingle v m, 1) : I.GA) := by
      funext m
      exact hform m
    rw [h1]
    have hm1 : Continuous fun m : UJ (I.ε v) => (Pi.mulSingle v m : I.Ginf) := by
      apply continuous_pi
      intro j
      by_cases hj : j = v
      · subst hj
        simp only [Pi.mulSingle_eq_same]
        exact continuous_id
      · simp only [Pi.mulSingle_eq_of_ne hj]
        exact continuous_const
    have hm2 : Continuous fun _ : UJ (I.ε v) => (1 : I.Gf) := continuous_const
    exact hm1.prodMk hm2
  have hfst : Continuous (Prod.fst : I.GA → I.Ginf) := continuous_fst
  have hf : Continuous (fun x : I.GA => x.1 v) := (continuous_apply v).comp hfst
  refine Function.LeftInverse.isClosedEmbedding ?_ hf hc
  intro m
  simp only [hform, Pi.mulSingle_eq_same]

theorem cusp_of_fibre_vanish : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  classical
  intro B d h hd hfib hloc hbig hfd T hT y
  obtain ⟨hT2, hLC, hSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have := hT2
  have := hLC
  have := hSC
  have hSF : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hLI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1⟩
  have hOP : (B.I.muA B.μf).IsOpenPosMeasure :=
    ⟨fun U hU hne => ((GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).2.2.2.2 U hU hne).ne'⟩
  have hFC : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hHaar : (B.I.muA B.μf).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hFC, toIsMulLeftInvariant := hLI, toIsOpenPosMeasure := hOP }
  have part1 : ∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W →
      ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0 := by
    intro f hf W hW ν hν x
    have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
    obtain ⟨-, ⟨Φ, hΦ, hbd⟩, hrep⟩ := GlobalTheory.T.reproducing_formula_discreteSeries_test_growth B d h hd hn hloc hbig hfd T hT y f hf
    obtain ⟨c, hc, hcle⟩ := GlobalTheory.T.truncatedLeastLatticeSize_bounded_below_unipotentRadical B.I W x hW
    obtain ⟨hνfin, -, hνc, hνinv⟩ := hν
    have := hνfin
    obtain ⟨hfc, hfinv, -⟩ := hf
    have hae : ∀ᵐ m ∂ν, m ∈ B.I.NA W := mem_ae_iff.2 hνc
    have hbound : ∀ᵐ m ∂ν, ∀ g, ‖phe B d g * f (m * x * g)‖ ≤
        c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * |Φ g| := by
      filter_upwards [hae] with m hm g
      have ht : c ≤ tau1 B.I (m * x) := hcle m hm
      have htpos : 0 < tau1 B.I (m * x) := lt_of_lt_of_le hc ht
      have hA : 0 ≤ (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_nonneg (inv_nonneg.2 htpos.le) _
      have hpow : (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) ≤ c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_le_pow_left₀ (inv_nonneg.2 htpos.le) (inv_anti₀ hc ht) _
      calc ‖phe B d g * f (m * x * g)‖ ≤ (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g :=
            hbd (m * x) g
        _ ≤ (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * |Φ g| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hA
        _ ≤ c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * |Φ g| := mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    obtain ⟨hint, heq⟩ := constTerm_repro (B.I.muA B.μf) ν f (phe B d) hfc
      (continuous_phe B d hd).measurable x _ (hΦ.abs.const_mul _) hbound hrep
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    obtain ⟨Wv, hWv, hWvNA⟩ := GlobalTheory.T.realUnipotentRadical_embeds_adelicRadical B.I W v hW
    obtain ⟨νv, hνv⟩ := GlobalTheory.Dec.exists_isHaarSub_NW (B.I.ε v) Wv
    have hincl : ∀ n : UJ (B.I.ε v), incl B.I v n = (Pi.mulSingle v n, 1) := fun n => rfl
    have hN0 : IsClosed ((GlobalTheory.Dec.nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) := by
      rw [GlobalTheory.Dec.coe_nwSub]
      exact GlobalTheory.Dec.isClosed_NW _ _
    have hν0 : IsHaarSub ((GlobalTheory.Dec.nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) νv := by
      rw [GlobalTheory.Dec.coe_nwSub]
      exact hνv
    obtain ⟨hcl, hhaar⟩ := isHaarSub_map_emb (incl B.I v) (isClosedEmbedding_incl B.I v) _ hN0 νv hν0
    have hFm : Measurable (fun z : B.I.GA => ∫ m, f (m * z) ∂ν) :=
      ((hfc.comp (continuous_snd.mul continuous_fst)).stronglyMeasurable.integral_prod_right').measurable
    have hφm : Measurable (fun z : B.I.GA => phe B d (x⁻¹ * z)) :=
      ((continuous_phe B d hd).comp (continuous_const_mul x⁻¹)).measurable
    have hinvF : ∀ m ∈ (GlobalTheory.Dec.nwSub (B.I.ε v) Wv).map (incl B.I v), ∀ z,
        (fun z : B.I.GA => ∫ m', f (m' * z) ∂ν) (m * z) = (fun z : B.I.GA => ∫ m', f (m' * z) ∂ν) z := by
      intro m hm z
      obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.mp hm
      have hnw : n0 ∈ NW (B.I.ε v) Wv := by
        have h' : n0 ∈ ((GlobalTheory.Dec.nwSub (B.I.ε v) Wv : Subgroup _) : Set (UJ (B.I.ε v))) := hn0
        rwa [GlobalTheory.Dec.coe_nwSub] at h'
      have hNA : incl B.I v n0 ∈ B.I.NA W := by
        rw [hincl]
        exact hWvNA n0 hnw
      have h3 := hνinv (fun m' => f (m' * z))
        (fun γ hγ w => by simp only [mul_assoc]; exact hfinv γ hγ.1 (w * z)) (incl B.I v n0) hNA
      simpa only [mul_assoc] using h3
    have hfibv : ∀ z, ∫ m, (fun z : B.I.GA => phe B d (x⁻¹ * z)) (m * z) ∂(νv.map (incl B.I v)) = 0 := by
      intro z
      rw [(isClosedEmbedding_incl B.I v).measurableEmbedding.integral_map]
      have h4 := hfib v Wv hWv νv hνv x⁻¹ z
      simp only [hincl, mul_assoc] at h4 ⊢
      exact h4
    have h0 := GlobalTheory.T.weil_integral_vanishing_of_fibre_integrals B.I.GA (B.I.muA B.μf) _ _ hcl hhaar _ _ hFm hφm hinvF hint hfibv
    rw [heq]
    exact h0
  refine ⟨part1, ?_⟩
  intro W hW ν hν
  have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
  have hbig32 : HBig B 32 h := by
    intro v
    have h1 : (0:ℝ) ≤ (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
    nlinarith [hbig v, h1]
  obtain ⟨yv, Fc, -, hspan, hFc, -⟩ := GlobalTheory.T.kernelB' B d h hd hn hloc hbig32 hfd T hT
  have key : ∀ z ∈ Submodule.span ℂ (Set.range yv), ∃ g : B.I.GA → ℂ, IsContRep B z g := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨Fc i, hFc i⟩
    | zero =>
      refine ⟨0, ?_⟩
      unfold GlobalTheory.Dec.IsContRep
      exact ⟨continuous_zero, fun _ _ _ => rfl, Lp.coeFn_zero ..⟩
    | add a b _ _ iha ihb =>
      obtain ⟨ga, hca, hia, hea⟩ := iha
      obtain ⟨gb, hcb, hib, heb⟩ := ihb
      refine ⟨ga + gb, ?_⟩
      unfold GlobalTheory.Dec.IsContRep
      refine ⟨hca.add hcb, fun γ hγ w => ?_, (Lp.coeFn_add a b).trans (hea.add heb)⟩
      simp only [Pi.add_apply, hia γ hγ w, hib γ hγ w]
    | smul r a _ iha =>
      obtain ⟨ga, hca, hia, hea⟩ := iha
      refine ⟨r • ga, ?_⟩
      unfold GlobalTheory.Dec.IsContRep
      refine ⟨hca.const_smul r, fun γ hγ w => ?_, (Lp.coeFn_smul r a).trans (hea.const_smul r)⟩
      simp only [Pi.smul_apply, hia γ hγ w]
  have hz : T y ∈ Submodule.span ℂ (Set.range yv) := by
    rw [hspan]
    exact LinearMap.mem_range_self _ y
  obtain ⟨f, hf⟩ := key (T y) hz
  obtain ⟨-, -, -, hae⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B (T y) f hf
  obtain ⟨hνfin, -⟩ := id hν
  filter_upwards [hae ν hνfin] with x hx
  rw [integral_congr_ae hx]
  exact part1 f hf W hW ν hν x

end GlobalTheory.CuspCore
