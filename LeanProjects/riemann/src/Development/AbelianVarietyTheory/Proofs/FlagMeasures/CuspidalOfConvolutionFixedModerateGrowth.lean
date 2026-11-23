import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReproducingFormulaFixedVectorModerateGrowthStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CuspFixed

theorem isHaarSub_map_emb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : IsHaarSub (N : Set H) ν) :
    IsClosed ((N.map ι : Subgroup G) : Set G) ∧ IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hS : ((N.map ι : Subgroup G) : Set G) = ι '' (N : Set H) := Subgroup.coe_map ι N
  obtain ⟨hne, hfc, hnull, hinv⟩ := hν
  refine ⟨by rw [hS]; exact hι.isClosedMap _ hN, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    rwa [Measure.map_eq_zero_iff hme.measurable.aemeasurable] at h0
  · refine ⟨fun K hK => ?_⟩
    rw [hme.map_apply]
    exact hfc.lt_top_of_isCompact (hι.isCompact_preimage hK)
  · rw [hme.map_apply, Set.preimage_compl, hS, Set.preimage_image_eq _ hι.injective]
    exact hnull
  · intro m hm
    rw [hS] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hcomm : (fun z : G => ι k * z) ∘ ι = ι ∘ (fun z : H => k * z) := by
      funext z
      simp only [Function.comp_apply, map_mul]
    rw [Measure.map_map (continuous_mul_left (ι k)).measurable hme.measurable, hcomm,
      ← Measure.map_map hme.measurable (continuous_mul_left k).measurable, hinv k hk]

theorem constTerm_repro {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [IsFiniteMeasure ν] (f φ : G → ℂ) (hf : Continuous f) (hφ : Measurable φ) (x : G)
    (Φ : G → ℝ) (hΦ : Integrable Φ μ) (hb : ∀ᵐ m ∂ν, ∀ g, ‖φ g * f (m * x * g)‖ ≤ Φ g)
    (hr : ∀ z, f z = ∫ g, φ g * f (z * g) ∂μ) :
    Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ ∧
      ∫ m, f (m * x) ∂ν = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ := by
  have hmeas : Measurable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) := by
    apply Measurable.mul
    · exact hφ.comp measurable_snd
    · exact (hf.comp (by fun_prop : Continuous fun p : G × G => p.1 * x * p.2)).measurable
  have hint : Integrable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) (ν.prod μ) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦ) hmeas.aestronglyMeasurable ?_
    have hae := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae hb
    filter_upwards [hae] with p hp
    simpa [Function.uncurry] using hp p.2
  have hH : (fun g => ∫ m, φ g * f (m * x * g) ∂ν) =
      fun g => (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) := by
    funext g
    beta_reduce
    rw [integral_const_mul, inv_mul_cancel_left, mul_comm]
    simp_rw [mul_assoc]
  have hI : Integrable (fun g => ∫ m, φ g * f (m * x * g) ∂ν) μ := hint.integral_prod_right
  rw [hH] at hI
  have hI2 := hI.comp_mul_left x⁻¹
  simp only [mul_inv_cancel_left] at hI2
  refine ⟨hI2, ?_⟩
  calc ∫ m, f (m * x) ∂ν = ∫ m, ∫ g, φ g * f (m * x * g) ∂μ ∂ν := by
        congr 1; funext m; exact hr (m * x)
    _ = ∫ g, ∫ m, φ g * f (m * x * g) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ g, (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) ∂μ := by rw [hH]
    _ = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ :=
        integral_mul_left_eq_self (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) x

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) : Continuous (phe B d) := by
  have he : Continuous B.e := (rowsAut_idem_elementary B).2.2.2
  have hv : ∀ v, Continuous (fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)) := by
    intro v
    have hc := ((hd v).2.1.2.2.1).2.2 (B.w v)
    exact hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))
      (fun g => (g v).2)
  have hph : Continuous (ph B d) := by
    unfold ph
    exact continuous_const.mul
      (continuous_star.comp (continuous_finset_prod _ fun v _ => continuous_const.inner (hv v)))
  unfold phe
  exact (hph.comp continuous_fst).mul (he.comp continuous_snd)

theorem one_le_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) : 1 ≤ I.n := by
  rcases Nat.eq_zero_or_pos I.n with h0 | hpos
  · exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.isLt (by omega)
  · exact hpos

open Classical in

noncomputable def incl (I : AutInst) (v : InfinitePlace I.F) : UJ (I.ε v) →* I.GA :=
  (MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun v => UJ (I.ε v)) v)

theorem isClosedEmbedding_incl (I : AutInst) (v : InfinitePlace I.F) : Topology.IsClosedEmbedding (incl I v) := by
  obtain ⟨hT2, -⟩ := CongTop.adelic_topology I
  haveI := hT2
  classical
  refine Function.LeftInverse.isClosedEmbedding (f := fun p : I.GA => p.1 v) ?_ ?_ ?_
  · intro m
    simp [incl]
  · exact (continuous_apply v).comp continuous_fst
  · exact (continuous_mulSingle (A := fun w : InfinitePlace I.F => UJ (I.ε w)) v).prodMk continuous_const

theorem cusp_of_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext y) := by
  intro B d h hd hfib hloc hbig T hT y f C hfix hrep hgr
  obtain ⟨hT2, hLC, hSC, -⟩ := CongTop.adelic_topology B.I
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI hHaar : (B.I.muA B.μf).IsHaarMeasure := by
    haveI h1 : ∀ w, (muG (B.I.ε w)).IsHaarMeasure := fun w => inferInstance
    haveI h2 : ∀ w, SigmaFinite (muG (B.I.ε w)) := fun w => inferInstance
    haveI h3 : (Measure.pi fun w => muG (B.I.ε w)).IsHaarMeasure := Measure.pi.isHaarMeasure _
    haveI h4 : SFinite (Measure.pi fun w => muG (B.I.ε w)) := inferInstance
    haveI h5 : SFinite B.μf := inferInstance
    unfold AutInst.muA
    exact Measure.prod.instIsHaarMeasure _ _
  have main : ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν →
      ∀ x, ∫ m, f (m * x) ∂ν = 0 := by
    intro W hW ν hνW x
    have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
    obtain ⟨⟨Φ, hΦi, hΦb⟩, hrepf⟩ := GlobalTheory.T.reproducing_formula_fixedVector_moderateGrowth B d h hd hn hloc hbig T hT y f C hfix hrep hgr
    obtain ⟨hfin, -, hconc, hinvN⟩ := hνW
    haveI := hfin
    obtain ⟨c, hc0, hc⟩ := exists_pos_le_tau1_mul_of_mem_NA_of_isIsot B.I W x hW
    have hbd : ∀ᵐ m ∂ν, ∀ g, ‖phe B d g * f (m * x * g)‖ ≤
        c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
      filter_upwards [mem_ae_iff.mpr hconc] with m hm g
      have ht : c ≤ tau1 B.I (m * x) := hc m hm
      have htpos : 0 < tau1 B.I (m * x) := hc0.trans_le ht
      have hb1 := hΦb (m * x) g
      have hpow : 0 < (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_pos (inv_pos.mpr htpos) _
      have hΦ0 : 0 ≤ Φ g := (mul_nonneg_iff_of_pos_left hpow).mp ((norm_nonneg _).trans hb1)
      exact hb1.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_anti₀ hc0 ht) _) hΦ0)
    obtain ⟨hint, heq⟩ := constTerm_repro (B.I.muA B.μf) ν f (phe B d) hrep.1
      (continuous_phe B d hd).measurable x (fun g => c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g)
      (hΦi.const_mul _) hbd hrepf
    rw [heq]
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    obtain ⟨Wv, hWv, hemb⟩ := RadEmb.radical_embeds B.I W v hW
    obtain ⟨νv, hνv⟩ := exists_isHaarSub_NW (B.I.ε v) Wv
    have hNcl : IsClosed ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) := by
      rw [coe_nwSub]
      exact isClosed_NW _ _
    have hνv' : IsHaarSub ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) νv := by
      rw [coe_nwSub]
      exact hνv
    have hemb' := isClosedEmbedding_incl B.I v
    obtain ⟨hNcl', hHs⟩ := isHaarSub_map_emb (incl B.I v) hemb' _ hNcl νv hνv'
    refine weilVanish B.I.GA (B.I.muA B.μf) _ _ hNcl' hHs (fun z => ∫ m, f (m * z) ∂ν)
      (fun z => phe B d (x⁻¹ * z)) ?_ ?_ ?_ hint ?_
    · exact (StronglyMeasurable.integral_prod_right' (ν := ν)
        (f := fun p : B.I.GA × B.I.GA => f (p.2 * p.1))
        (hrep.1.comp (continuous_snd.mul continuous_fst)).stronglyMeasurable).measurable
    · exact ((continuous_phe B d hd).comp (continuous_const.mul continuous_id)).measurable
    · intro n hn z
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
      have hk' : k ∈ NW (B.I.ε v) Wv := by
        rw [← coe_nwSub]
        exact hk
      have hkNA : incl B.I v k ∈ B.I.NA W := hemb k hk'
      have hsh := hinvN (fun m => f (m * z)) (fun γ hγ w => by
        show f (γ * w * z) = f (w * z)
        rw [mul_assoc]
        exact hrep.2.1 γ hγ.1 (w * z)) (incl B.I v k) hkNA
      show ∫ m, f (m * (incl B.I v k * z)) ∂ν = ∫ m, f (m * z) ∂ν
      simpa only [mul_assoc] using hsh
    · intro z
      rw [hemb'.measurableEmbedding.integral_map]
      have hz := hfib v Wv hWv νv hνv x⁻¹ z
      simp only [← mul_assoc]
      exact hz
  refine ⟨main, ?_⟩
  intro W hW ν hνW
  have hae := (ExtContRep.ext_ae_eq_contRep B y f hrep).2.2.2 ν hνW.1
  filter_upwards [hae] with x hx
  rw [integral_congr_ae hx]
  exact main W hW ν hνW x

end GlobalTheory.CuspFixed
