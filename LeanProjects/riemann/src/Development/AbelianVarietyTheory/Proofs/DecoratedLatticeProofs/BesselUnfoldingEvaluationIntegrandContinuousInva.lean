import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Unf.EvalInv

section General

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [MeasurableSpace H] [BorelSpace H] {μ : Measure H} [μ.IsHaarMeasure] {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}

omit [LocallyCompactSpace H] in

theorem fund_lt_top {C : Set H} (hC : IsCompact C) (hcov : ∀ g, ∃ γ ∈ Γ, γ * g ∈ C)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • C) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : μ 𝓕 ≤ μ C := by
    calc μ 𝓕 = μ ((⋃ g : Γ, (g • C)) ∩ 𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = μ (⋃ g : Γ, (g • C ∩ 𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : Γ, μ (g • C ∩ 𝓕) := measure_iUnion_le _
      _ = μ C := (h𝓕.measure_eq_tsum C).symm
  exact hle.trans_lt hC.measure_lt_top

theorem mean_mul_right [SecondCountableTopology H] (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) (f : H → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (r : H) : ∫ x in 𝓕, f (x * r) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have hm := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * r) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (· * r) μ) μ
  have hq : Measure.QuasiMeasurePreserving (· * r) μ μ :=
    ⟨measurable_mul_const r, by rw [hm]; exact Measure.smul_absolutelyContinuous⟩
  have h' : IsFundamentalDomain Γ ((· * r) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id fun g x => by
      simp [Subgroup.smul_def, mul_assoc]
  have he : MeasurableEmbedding (· * r) := (MeasurableEquiv.mulRight r).measurableEmbedding
  have h1 : μ ((· * r) ⁻¹' 𝓕) = c * μ 𝓕 := by
    rw [← he.map_apply]
    exact (congrArg (fun m : Measure H => m 𝓕) hm).trans rfl
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hc : c = 1 := by
    rw [h'.measure_eq h𝓕] at h1
    have : (c : ENNReal) = 1 := by
      refine (ENNReal.mul_left_inj h0 hfin.ne).1 ?_
      rw [← h1, one_mul]
    exact_mod_cast this
  have hp : MeasurePreserving (· * r) μ μ := ⟨measurable_mul_const r, by rw [hm, hc, one_smul]⟩
  rw [← hp.setIntegral_preimage_emb he f 𝓕]
  exact h𝓕.setIntegral_eq h' fun g x => by
    simpa [Subgroup.smul_def, mul_assoc] using hf g g.2 (x * r)

omit [LocallyCompactSpace H] in

theorem mean_continuous [SecondCountableTopology H] {C : Set H} (hC : IsCompact C) (hcov : ∀ g, ∃ γ ∈ Γ, γ * g ∈ C)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {P : Type} [TopologicalSpace P] [FirstCountableTopology P]
    [LocallyCompactSpace P] (K : H → P → ℂ) (hK : Continuous fun q : H × P => K q.1 q.2)
    (hinv : ∀ γ ∈ Γ, ∀ x p, K (γ * x) p = K x p) :
    (∀ p, IntegrableOn (fun x => K x p) 𝓕 μ) ∧ Continuous fun p => ∫ x in 𝓕, K x p ∂μ := by
  have hfin := fund_lt_top hC hcov h𝓕
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  have hb : ∀ p₀, ∃ B : ℝ, ∀ᶠ p in nhds p₀, ∀ x, ‖K x p‖ ≤ B := fun p₀ => by
    obtain ⟨U, hU, hU'⟩ := exists_compact_mem_nhds p₀
    obtain ⟨B, hB⟩ := (hC.prod hU).exists_bound_of_continuousOn hK.continuousOn
    refine ⟨B, Filter.mem_of_superset hU' fun p hp x => ?_⟩
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hinv γ hγ x p]
    exact hB (γ * x, p) ⟨hk, hp⟩
  have hm : ∀ p, AEStronglyMeasurable (fun x => K x p) (μ.restrict 𝓕) := fun p =>
    (hK.comp (Continuous.prodMk_left p)).aestronglyMeasurable
  refine ⟨fun p => ?_, continuous_iff_continuousAt.2 fun p₀ => ?_⟩
  · obtain ⟨B, hB⟩ := hb p
    exact Integrable.of_bound (hm p) B (Filter.Eventually.of_forall hB.self_of_nhds)
  · obtain ⟨B, hB⟩ := hb p₀
    exact continuousAt_of_dominated (bound := fun _ => B) (Filter.Eventually.of_forall hm)
      (hB.mono fun p hp => Filter.Eventually.of_forall hp) (integrable_const B)
      (Filter.Eventually.of_forall fun x => (hK.comp (Continuous.prodMk_right x)).continuousAt)

end General

variable {D : D7}

def orthZero (S : HSp D) : OrthDec S S (diagSp D 0 ![] 0 0) where
  iA := 1
  iB := 0
  isoA := by simp
  isoB := funext fun i => i.elim0
  orth := funext fun i => i.elim0
  rank_add := rfl

theorem jac_cocompact {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (hc : CoCpt W₀) :
    ∃ C : Set (jacGrp d), IsCompact C ∧ ∀ g, ∃ γ ∈ (GQ W ⊓ jacGrp d).subgroupOf (jacGrp d), γ * g ∈ C := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have dec := flag_jacobi_structure D W W₀ ρ d
  obtain ⟨K₀, hK₀, h₀⟩ := hc
  obtain ⟨K, hK, hN⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D W ρ d.e (isIsoSub_e d)).1
  let m : flagN d × GA D W₀ → jacGrp d := fun p =>
    ⟨p.1.1 * d.emb0 p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right ⟨p.2, rfl⟩)⟩
  have hm : Continuous m :=
    ((continuous_subtype_val.comp continuous_fst).mul (d.continuous_embed.comp continuous_snd)).subtype_mk _
  refine ⟨m '' (K ×ˢ K₀), (hK.prod hK₀).image hm, fun g => ?_⟩
  obtain ⟨n, hn, h, hg⟩ := (dec.2.2.2.1 g.1).1 g.2
  obtain ⟨δ, hδ, hk⟩ := h₀ h
  obtain ⟨γ, hγ, k, hkK, e⟩ := hN ⟨_, dec.2.2.2.2.1 n hn δ⟩
  have e' : d.emb0 δ * n * (d.emb0 δ)⁻¹ = γ.1 * k.1 := congrArg Subtype.val e
  have hmem : γ.1⁻¹ * d.emb0 δ ∈ jacGrp d :=
    mul_mem (inv_mem (Subgroup.mem_sup_left γ.2)) (Subgroup.mem_sup_right ⟨δ, rfl⟩)
  have hγ' : γ.1 ∈ GQ W := hγ
  have hq : γ.1⁻¹ * d.emb0 δ ∈ GQ W := mul_mem (inv_mem hγ') (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hδ)
  refine ⟨⟨_, hmem⟩, ⟨hq, hmem⟩, (k, δ * h), ⟨hkK, hk⟩, Subtype.ext ?_⟩
  change k.1 * d.emb0 (δ * h) = γ.1⁻¹ * d.emb0 δ * g.1
  rw [hg, map_mul, show k.1 = γ.1⁻¹ * (d.emb0 δ * n * (d.emb0 δ)⁻¹) by rw [e']; group]
  group

theorem jac_mean {ρ : ℕ} (J : JacLev D ρ) (K : GA D J.W → GA D J.W → ℂ)
    (hK : Continuous fun q : jacGrp J.d × GA D J.W => K q.1 q.2)
    (hinv : ∀ γ ∈ GQ J.W, γ ∈ jacGrp J.d → ∀ r ∈ jacGrp J.d, ∀ p, K (γ * r) p = K r p) :
    (Continuous fun p => ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, K (n.1 * J.d.emb0 h) p ∂J.vN.ν ∂J.v0.μ) ∧
    ∀ r ∈ jacGrp J.d, ∀ p p', (∀ x ∈ jacGrp J.d, K x p' = K (x * r) p) →
      ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, K (n.1 * J.d.emb0 h) p' ∂J.vN.ν ∂J.v0.μ =
        ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, K (n.1 * J.d.emb0 h) p ∂J.vN.ν ∂J.v0.μ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  have dec := flag_jacobi_structure D J.W J.W₀ ρ J.d
  have base := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  obtain ⟨⟨hcl, hhaar⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ _ ρ J.d (orthZero J.W₀) J.vN.ν J.vN.𝓝 J.vN.unit
  have hμ := hhaar J.v0.μ J.v0.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D J.W J.W₀ (flagN J.d) J.d.emb0 J.d.continuous_embed
    (GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D J.W J.W₀ ρ J.d).1 dec.2.2.2.2.1 dec.2.2.2.2.2.1 base.2.2.2.2.2 J.v0 J.vN.ν J.vN.𝓝 J.vN.unit.1
    J.vN.unit.2.1 hμ
  obtain ⟨C, hC, hcov⟩ := jac_cocompact J.d J.cpt
  have : LocallyCompactSpace (jacGrp J.d) := hcl.locallyCompactSpace
  have : SecondCountableTopology (jacGrp J.d) :=
    TopologicalSpace.Subtype.secondCountableTopology (jacGrp J.d : Set (GA D J.W))
  have : Countable ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) :=
    Function.Injective.countable (f := fun x => (⟨x.1.1, x.2.1⟩ : GQ J.W)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ J.W => z.1) hab))
  have : J.μR.IsHaarMeasure := hμ
  have h𝓡' : IsFundamentalDomain (α := jacGrp J.d) ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) 𝓡 J.μR := h𝓡
  have hinv' : ∀ γ ∈ (GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d), ∀ (x : jacGrp J.d) p,
      K (γ * x : jacGrp J.d) p = K x p := fun γ hγ x p => hinv γ hγ.1 γ.2 x x.2 p
  obtain ⟨hI, hcont⟩ := mean_continuous hC hcov h𝓡' (fun (x : jacGrp J.d) p => K x p) hK hinv'
  have hme : MeasurableEmbedding (Subtype.val : jacGrp J.d → GA D J.W) :=
    MeasurableEmbedding.subtype_coe hcl.measurableSet
  have key : ∀ p, ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, K (n.1 * J.d.emb0 h) p ∂J.vN.ν ∂J.v0.μ =
      ∫ x : jacGrp J.d in 𝓡, K x p ∂J.μR := fun p => by
    let f : GA D J.W → ℂ := Function.extend Subtype.val (fun x : jacGrp J.d => K x p) 0
    have hf : ∀ x : jacGrp J.d, f x = K x p := fun x => Subtype.val_injective.extend_apply _ _ x
    have hfm : Measurable f :=
      hme.measurable_extend (hK.comp (Continuous.prodMk_left p)).measurable measurable_const
    have hf' : ∀ (n : flagN J.d) h, f (n.1 * J.d.emb0 h) = K (n.1 * J.d.emb0 h) p := fun n h =>
      hf ⟨_, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩
    obtain ⟨h1, h2⟩ := hint f hfm
    have h4 := hI p
    simp only [← hf] at h4
    have h3 := h2 (h1.1 h4)
    simp only [hf'] at h3
    rw [← h3]
    simp only [← hf]
    rfl
  simp only [key]
  refine ⟨hcont, fun r hr p p' h => ?_⟩
  rw [← mean_mul_right h𝓡' (fund_lt_top hC hcov h𝓡') (fun x => K x p) (fun γ hγ x => hinv' γ hγ x p) ⟨r, hr⟩]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => h x x.2)

section Alg

variable {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ}

theorem yZero_rat (S : HSp D) (ρ : ℕ) (z : Fin S.rank → D.host.E) : yZero S ρ z ∈ ratMx D S.rank ρ := by
  refine neg_mem ⟨vecMulVec z fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0, ?_⟩
  rw [zEll, GlobalTheory.CharLaws.ell_eq]
  funext i j
  exact map_mul (incA D) _ _

theorem jacT_rat (hψ : IsStdChar D ψ (-1)) {T T₀ : HSp D} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ}
    (hy : y ∈ ratMx D S.rank ρ) {n : GA D T} (hn : n ∈ GQ T) {f : WO S T₀ → ℂ} (hf : IsThetaFunO ψ S T₀ f) :
    jacT ψ d S y n f 0 = f 0 := by
  have h1 : d.incAdj S y ∈ ratMx D _ _ := ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))
  have h2 : mt T n⁻¹ ⬝ d.incAdj S y ∈ ratMx D _ _ := ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn)) h1
  obtain ⟨δ, hδ⟩ : ptT d S y n ∈ ratMx D _ _ := ratMx_mul (rat_mem _) h2
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2
  have h := hf.quasi δ 0
  rw [show ratW T₀ S δ = ptT d S y n from hδ, add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at h
  rw [jacT, cenT, ha, hψ.1.2.2.1, one_smul, heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add, h]

variable {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

abbrev ev (Ψ : WO B.V J.W → ℂ) (x : Mx D J.W.rank ρ) : WO B.V₀ J.W₀ → ℂ :=
  evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ x (yZero B.V₀ ρ (vecB B.o B.ζ))

theorem ev_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    IsThetaFunO ψ B.V₀ J.W₀ (ev s Ψ x) :=
  (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).2 _ _ _ _ J.d _ _ s.vT.covol _
    ((GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol _ hΨ x) _

theorem om_mul (a b : GA D B.V) (g h : GA D J.W) (Ψ : WO B.V J.W → ℂ) :
    s.om (a * b, g * h) Ψ = s.om (a, g) (s.om (b, h) Ψ) := by
  rw [← Prod.mk_mul_mk, map_mul]; rfl

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem ev_om {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (u : UX D ρ) (h₀ : GA D B.A) {n : GA D J.W}
    (hn : n ∈ flagN J.d) (h' : GA D J.W₀) :
    ev s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (mt J.W (n * J.d.emb0 h') ⬝ (J.d.jX ⬝ u.1.1)) =
      s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (ev s Ψ (J.d.jX ⬝ u.1.1))) := by
  have dec := flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨v, hv, b, c, rfl⟩ := (dec.1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := (dec.2.1 _).2 ⟨b, c, rfl⟩
  have e1 : mt J.W (J.d.levi v * (J.d.nB b * J.d.nC c) * J.d.emb0 h') ⬝ (J.d.jX ⬝ u.1.1) =
      xZero J.d ⬝ ((⟨v, hv⟩ : UX D ρ) * u).1.1 := by
    rw [← Matrix.mul_assoc, mt_mul, mt_mul, mt_mul, Matrix.mul_assoc _ _ J.d.jX, J.d.wittDecomp_anisotropicEmbedding_inclX,
      Matrix.mul_assoc _ _ J.d.jX, Matrix.mul_assoc _ _ J.d.jX, J.d.nC_jX, J.d.nB_jX, J.d.levi_jX, Matrix.mul_assoc]
    rfl
  have e2 := (GlobalTheory.T.doubleMixedModel_baseValue_equivariant D ψ ρ B J s om' hom _
    (s.weil.om_pres (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') _ hΨ)).2 ((⟨v, hv⟩ : UX D ρ) * u) ⟨v, hv⟩
  rw [inv_mul_cancel_left, ← om_mul, one_mul, ← mul_assoc,
    (GlobalTheory.T.doubleMixedModel_baseValue_equivariant D ψ ρ B J s om' hom _ hΨ).1 u h₀ _ hr h'] at e2
  rw [e1, opA, jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul _ _ hv)]
  exact e2

def ker (φ : GA D B.A → ℂ) (Φ : WO B.V J.W → ℂ) (h₀ : GA D B.A) (r h : GA D J.W) : ℂ :=
  φ h₀ * ev s (s.om (embA B.d B.o h₀, r * h) Φ) (mt J.W r ⬝ J.d.jX) 0

omit hom in
theorem exists_uni {r : GA D J.W} (hr : r ∈ jacGrp J.d) : ∃ u : UX D ρ, mt J.W r ⬝ J.d.jX = J.d.jX ⬝ u.1.1 := by
  rw [← (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.1] at hr
  obtain ⟨u, hu, h⟩ := hr
  exact ⟨⟨u, hu⟩, h⟩

variable {φ : GA D B.A → ℂ} {Φ : WO B.V J.W → ℂ} (hφ : IsContAut B.A φ) (hΦ : IsThetaFunO ψ B.V J.W Φ)
include hΦ

theorem ker_jac {γ : GA D J.W} (hγ : γ ∈ GQ J.W) (hγ' : γ ∈ jacGrp J.d) {r : GA D J.W} (hr : r ∈ jacGrp J.d) (h₀ h) :
    ker s φ Φ h₀ (γ * r) h = ker s φ Φ h₀ r h := by
  obtain ⟨u, hu⟩ := exists_uni hr
  obtain ⟨n, hn, δ, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).2.2.2.1 γ).1 hγ'
  obtain ⟨hnq, hδ⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn δ).1 hγ
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, r * h) _ hΦ
  have e := ev_om s hom hΨ u 1 hn δ
  rw [← om_mul, map_one, one_mul, ← hu, ← Matrix.mul_assoc, ← mt_mul, ← mul_assoc, Prod.mk_one_one, map_one,
    Prod.mk_one_one, map_one, Module.End.one_apply] at e
  rw [ker, ker, e, opA, jacT_rat s.weil.std J.d B.V₀ (yZero_rat _ _ _) hnq (s.weil₀.om_pres _ _ (ev_theta s hΨ _)),
    s.weil₀.om_aut 1 (one_mem _) δ hδ _ (ev_theta s hΨ _)]

theorem ker_eq {n : GA D J.W} (hn : n ∈ flagN J.d) (h' h₀ h) : ker s φ Φ h₀ (n * J.d.emb0 h') h =
    φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (evalBF s (s.om (1, h) Φ)) h₀ n h' := by
  have e := ev_om s hom (s.weil.om_pres (1, h) _ hΦ) 1 h₀ hn h'
  rw [← om_mul, mul_one, show J.d.jX ⬝ (1 : UX D ρ).1.1 = J.d.jX from Matrix.mul_one _] at e
  rw [ker, e]
  rfl

include hφ

theorem ker_left {γ : GA D B.A} (hγ : γ ∈ GQ B.A) {r : GA D J.W} (hr : r ∈ jacGrp J.d) (h₀ h) :
    ker s φ Φ (γ * h₀) r h = ker s φ Φ h₀ r h := by
  obtain ⟨u, hu⟩ := exists_uni hr
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, r * h) _ hΦ
  have e := ev_om s hom hΨ u γ (one_mem _) 1
  rw [← om_mul, map_one, one_mul, one_mul, mt_one, Matrix.one_mul, ← hu, ← map_mul, opA, jacT_one, id, Prod.mk_one_one,
    map_one, Module.End.one_apply] at e
  rw [ker, ker, e, hφ.1 γ hγ, s.weil₀.om_aut _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (ev_theta s hΨ _)]

omit hom in
theorem ker_cont : Continuous fun q : GA D B.A × jacGrp J.d × GA D J.W => ker s φ Φ q.1 q.2.1 q.2.2 := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).2
  have hA : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hr : Continuous fun q : GA D B.A × jacGrp J.d × GA D J.W => (q.2.1 : GA D J.W) :=
    continuous_subtype_val.comp continuous_snd.fst
  have hx : Continuous fun q : GA D B.A × jacGrp J.d × GA D J.W => (mt J.W q.2.1 ⬝ J.d.jX : Mx D J.W.rank ρ) :=
    ((continuous_mt J.W).comp hr).matrix_mul continuous_const
  have hp : Continuous fun q : GA D B.A × jacGrp J.d × GA D J.W =>
      (((embA B.d B.o q.1, q.2.1 * q.2.2), mt J.W q.2.1 ⬝ J.d.jX, yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
    ((hA.comp continuous_fst).prodMk (hr.mul continuous_snd.snd)).prodMk (hx.prodMk continuous_const)
  have h2 := h.comp hp
  simp only [Function.comp_def] at h2
  exact (hφ.2.comp continuous_fst).mul h2

end Alg

theorem psiFlag_jac {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} {W W₀ : HSp D} (d : HypDec W W₀ ρ)
    {γ : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ ∈ jacGrp d) {r : GA D W} (hr : r ∈ jacGrp d) :
    psiFlag ψ d (γ * r) = psiFlag ψ d r := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  obtain ⟨n, hn, δ, rfl⟩ := (dec.2.2.2.1 γ).1 hγ'
  obtain ⟨m, hm, k, rfl⟩ := (dec.2.2.2.1 r).1 hr
  obtain ⟨hnq, -⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D W W₀ ρ d).2.2.2.2.2 n hn δ).1 hγ
  have h1 : ∀ g k, psiFlag ψ d (g * d.emb0 k) = psiFlag ψ d g := fun g k => by
    rw [psiFlag, psiFlag, blockX, blockX, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  rw [show n * d.emb0 δ * (m * d.emb0 k) = n * (d.emb0 δ * m * (d.emb0 δ)⁻¹) * d.emb0 (δ * k) by rw [map_mul]; group,
    h1, h1, psiFlag_mul d ψ hn (dec.2.2.2.2.1 m hm δ), GlobalTheory.CharLaws.psiFlag_conj, psiFlag_eq d ψ n,
    GlobalTheory.CharLaws.psiBes_rat ψ d hψ.1.2.2.1 1 0 hnq, one_mul]

end GlobalTheory.Unf.EvalInv

namespace GlobalTheory.Unf

open EvalInv

theorem evalIntegrand_continuous_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) ∧ ∀ r ∈ radX J.d ⊔ J.d.emb0.range, ∀ h, J.perAll ψ B s.om₀ φ (rTrans (r * h) G) (evalBF s (s.om (1, (r * h)) Φ)) = J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let K : GA D J.W → GA D J.W → ℂ := fun r h =>
    G (r * h) * star (psiFlag ψ J.d r) * ∫ h₀ in B.vA.𝓕, ker s φ Φ h₀ r h ∂B.vA.μ
  have hper : ∀ h, J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) =
      ∫ h' in J.v0.𝓕, ∫ n in J.vN.𝓝, K (n.1 * J.d.emb0 h') h ∂J.vN.ν ∂J.v0.μ := fun h => by
    unfold JacLev.perAll fjAll
    congr 1; funext h'; congr 1; funext n
    have h1 : psiFlag ψ J.d (n.1 * J.d.emb0 h') = psiFlag ψ J.d n.1 := by
      rw [psiFlag, psiFlag, blockX, blockX, mt_mul, Matrix.mul_assoc, J.d.wittDecomp_anisotropicEmbedding_inclX]
    simp only [K, ker_eq s hom hΦ n.2, h1]
    rfl
  have hpsi : Continuous (psiFlag ψ J.d) := by
    rw [show psiFlag ψ J.d = psiBes ψ J.d 1 0 from funext (psiFlag_eq J.d ψ)]
    exact GlobalTheory.CharLaws.continuous_psiBes ψ J.d s.weil.std.1.1 1 0
  have hK : Continuous fun q : jacGrp J.d × GA D J.W => K q.1 q.2 := by
    have hr : Continuous fun q : jacGrp J.d × GA D J.W => (q.1 : GA D J.W) := continuous_subtype_val.comp continuous_fst
    exact ((hG.continuous.comp (hr.mul continuous_snd)).mul (hpsi.comp hr).star).mul
      (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (jacGrp J.d × GA D J.W) (fun h₀ q => ker s φ Φ h₀ q.1 q.2) (ker_cont s hφ hΦ)
        fun γ hγ h₀ q => ker_left s hom hφ hΦ hγ q.1.2 h₀ q.2).2.1
  obtain ⟨h1, h2⟩ := jac_mean J K hK fun γ hγ hγ' r hr p => by
    simp only [K, mul_assoc γ r p, hG.left hγ, psiFlag_jac s.weil.std J.d hγ hγ' hr, ker_jac s hom hΦ hγ hγ' hr]
  simp only [hper]
  refine ⟨h1, fun r hr h => h2 r (sup_le_sup_right (inf_le_left (b := fixer J.W J.d.jX)) _ hr) h (r * h) fun x _ => ?_⟩
  have hs : r ∈ stabX J.d :=
    sup_le (radX_le_stabX J.d) (by rintro _ ⟨k, rfl⟩; exact wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d k) hr
  have e : mt J.W (x * r) ⬝ J.d.jX = mt J.W x ⬝ J.d.jX := by rw [mt_mul, Matrix.mul_assoc, mem_fixer.1 hs]
  simp only [K, ker, psiFlag, blockX, e, mul_assoc x r h]

end GlobalTheory.Unf

end
