import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Unf.cut_gram_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS vN x₀ Th hB hTh Ψ hΨ
  have lemR : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent D ψ V V₀ W ρ d χV χW om om' hW hW' vS x₀ hB
  have lemQ : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne D ψ hW.std V V₀ W ρ d x₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hH, hFD, h1⟩ := vN.unit

  have hBc : ∀ (c : skewA D ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∀ x,
      term ψ d W vS (om (d.nC c, 1) Φ) x = ψ (d.qS W c (rat x)) * term ψ d W vS Φ x := by
    intro c Φ hΦ x
    have h := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ).1 x 0 1 c
    rw [d.nB_zero, Subgroup.coe_one, map_one, mul_one, mul_one] at h
    rw [h]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, Matrix.mul_zero]
    rfl
  have hsplit : ∀ g h : GA D V, om (g * h, 1) Ψ = om (g, 1) (om (h, 1) Ψ) := by
    intro g h
    rw [show ((g * h, (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply]
  let F : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} → flagN d → ℂ :=
    fun i n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
  let a : skewA D ρ → Matrix (Fin W.rank) (Fin ρ) D.host.E → ℂ :=
    fun c x => star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x))
  have hE : ∀ i c (n : flagN d), F i (⟨d.nC c, d.nC_mem_NFlag c⟩ * n) = a c i.1 * F i n := by
    intro i c n
    simp only [F, a, Subgroup.coe_mul]
    rw [hTh.cen c n.1 n.2, hsplit, hBc c _ (hW.om_pres _ _ hΨ)]
    ring

  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS
  obtain ⟨-, hM⟩ := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  obtain ⟨-, hcl, hnorm, K, hK, hKc⟩ := hM (centre d) (Or.inl rfl)
  have hdisc : DiscreteTopology (NFlagQ V d.e) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V))
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h)))
  have hcl' : IsClosed (((centre d).subgroupOf (flagN d) : Subgroup (flagN d)) : Set (flagN d)) := by
    rw [Subgroup.coe_subgroupOf]; exact hcl.preimage continuous_subtype_val
  have hcpt : ∃ K' : Set ((centre d).subgroupOf (flagN d)), IsCompact K' ∧
      ∀ m, ∃ γ ∈ (NFlagQ V d.e).subgroupOf ((centre d).subgroupOf (flagN d)), ∃ k ∈ K', m = γ * k := by
    let φ : centre d → (centre d).subgroupOf (flagN d) := fun c =>
      ⟨⟨c.1, (hM (centre d) (Or.inl rfl)).1 c.2⟩, Subgroup.mem_subgroupOf.2 c.2⟩
    have hφ : Continuous φ := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
    refine ⟨φ '' K, hK.image hφ, fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨φ γ, ?_, φ k, ⟨k, hk, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hγ))
    · refine Subtype.ext (Subtype.ext ?_)
      change m.1.1 = γ.1 * k.1
      exact congrArg Subtype.val e
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    (hTh.cont.mul ((hT Ψ hΨ).2.2.2.1 i.1 |>.comp (continuous_subtype_val.prodMk continuous_const))).measurable
  have hbd : ∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B := by
    obtain ⟨K, hK, hKc⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D V ρ d.e (isIsoSub_e d)).1
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hTh.cont.continuousOn
    obtain ⟨C, A, hCA⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
    refine ⟨M.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal, fun n => ?_⟩
    have hTn : ‖Th n.1‖ₑ ≤ ENNReal.ofReal M := by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      rw [Subgroup.coe_mul, hTh.left γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 k.1 k.2, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM k hk)
    have hS := hCA 1 1 n.1 n.2
    rw [mul_one] at hS
    calc ∑' i, ‖F i n‖ₑ = ‖Th n.1‖ₑ * ∑' i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀},
          ‖term ψ d W vS (om (n.1, 1) Ψ) i.1‖ₑ := by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun i => enorm_mul _ _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
          mul_le_mul' hTn ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans hS)
      _ = _ := by rw [ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul]
  have hinv : ∀ γ ∈ NFlagQ V d.e, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n := by
    intro γ hγ n
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit, tsum_mul_left, tsum_mul_left,
      lemR γ.1 hγ' γ.2 _ (hW.om_pres _ _ hΨ)]
  have hcinv : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∀ γ ∈ NFlagQ V d.e, γ ∈ (centre d).subgroupOf (flagN d) → ∀ n,
      ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 (γ * n) =
        ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 n := by
    intro c γ hγ hγM n
    refine tsum_congr fun i => ?_
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hγM
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit]
    congr 1
    refine (hT _ (hW.om_pres _ _ hΨ)).2.1 γ.1 hγ' γ.2 i.1.1 i.1.1 ?_
    rw [blockX_of_fix d (mem_fixer.2 (hc' ▸ d.nC_jX c')), Matrix.mul_one]
  have heig : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∃ u ∈ (centre d).subgroupOf (flagN d), ∃ a : ℂ, a ≠ 1 ∧ ∀ i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, id i = c →
      ∀ m ∈ (centre d).subgroupOf (flagN d), ∀ n, F i (m * u * n) = a * F i (m * n) := by
    intro c
    obtain ⟨c', hc'⟩ := lemQ c.1 c.2
    refine ⟨⟨d.nC c', d.nC_mem_NFlag c'⟩, Subgroup.mem_subgroupOf.2 ⟨c', rfl⟩, a c' c.1, hc', ?_⟩
    intro i hi m hm n
    subst hi
    obtain ⟨c'', hc''⟩ := Subgroup.mem_subgroupOf.1 hm
    have : m = ⟨d.nC c'', d.nC_mem_NFlag c''⟩ := Subtype.ext hc''.symm
    subst this
    rw [mul_assoc, hE, hE, hE]
    simp only [id]
    ring
  exact GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν (NFlagQ V d.e) ((centre d).subgroupOf (flagN d)) j4 hdisc hnorm hcl' hcpt
    vN.𝓝 hFD (by rw [h1]; exact ENNReal.one_ne_top) _ _ id F hmeas hbd hinv hcinv heig
