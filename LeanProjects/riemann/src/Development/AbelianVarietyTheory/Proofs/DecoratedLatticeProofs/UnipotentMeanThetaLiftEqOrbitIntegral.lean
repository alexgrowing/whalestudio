import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMeanEqOrbitSumMeanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

namespace GlobalTheory.Unf

theorem mean_lift_eq_orbit_integral : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → (∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤) ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 ∂(vN.ν.prod vW.μ) := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN vW x₀ Th hB hTh G Φ hG hΦ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  haveI := vN.unit.1
  haveI := vW.haar
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [show ((g, h) : GA D V × GA D W) = (g, 1) * (1, h) by simp, map_mul, Module.End.mul_apply]
  have hsum : ∀ (n : flagN d) (h : GA D W), HasSum (term ψ d W vS (om (n.1, h) Φ)) (om (n.1, h) Φ 0) :=
    fun n h => (hT _ (hw.om_pres _ _ hΦ)).2.2.2.2

  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Φ hΦ
  have hbd : ∀ (n : flagN d) (h : GA D W), ∑' x, ‖term ψ d W vS (om (n.1, h) Φ) x‖ₑ ≤
      ENNReal.ofReal (max C 0 * quotHeight W h ^ A) := fun n h => by
    have := hC 1 h n.1 n.2
    rw [mul_one, height_one, one_mul] at this
    exact this.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (quotHeight_pos W h).le _)))
  obtain ⟨B, hBd⟩ := hG.2.2 A
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos W 1).le _)).trans (hBd 1)

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hThb 1)

  have hGt : ∀ (n : flagN d) (h : GA D W), ‖G h‖ₑ * ∑' x, ‖term ψ d W vS (om (n.1, h) Φ) x‖ₑ ≤
      ENNReal.ofReal (max C 0 * B) := fun n h => by
    refine (mul_le_mul' le_rfl (hbd n h)).trans ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖G h‖ * (max C 0 * quotHeight W h ^ A) = max C 0 * (‖G h‖ * quotHeight W h ^ A) := by ring
      _ ≤ max C 0 * B := mul_le_mul_of_nonneg_left (hBd h) (le_max_right _ _)
  have hall : ∀ (n : flagN d) (h : GA D W) (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)),
      ∑' y : S, ‖Th n.1 * G h * term ψ d W vS (om (n.1, h) Φ) y.1‖ₑ ≤ ENNReal.ofReal (M * (max C 0 * B)) := by
    intro n h S
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, mul_assoc, ENNReal.ofReal_mul hM0]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hThb n)
    · exact (mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)).trans (hGt n h)
  have hK0 : 0 ≤ M * (max C 0 * B) := mul_nonneg hM0 (mul_nonneg (le_max_right _ _) hB0)
  have hnorm : ∀ (n : flagN d) (h : GA D W), ‖om (n.1, h) Φ 0‖ * ‖G h‖ ≤ max C 0 * B := fun n h => by
    have h1 : ‖om (n.1, h) Φ 0‖ₑ * ‖G h‖ₑ ≤ ENNReal.ofReal (max C 0 * B) := by
      rw [mul_comm, ← (hsum n h).tsum_eq]
      exact (mul_le_mul' le_rfl enorm_tsum_le_tsum_enorm).trans (hGt n h)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_mul, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) hB0)] at h2
  haveI : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vW.μ.restrict vW.𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund)
  have hfin : (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) ≠ ⊤ := by
    rw [Measure.prod_prod, vN.unit.2.2, one_mul]
    exact GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund
  refine ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M * (max C 0 * B))) hfin) ?_, ?_⟩
  · calc _ ≤ ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ENNReal.ofReal (M * (max C 0 * B)) ∂(vN.ν.prod vW.μ) :=
          lintegral_mono fun p => hall p.1 p.2 _
      _ = _ := setLIntegral_const _ _
  have hF : Integrable (fun p : flagN d × GA D W => Th p.1.1 * (om (p.1.1, p.2) Φ 0 * G p.2))
      ((vN.ν.restrict vN.𝓝).prod (vW.μ.restrict vW.𝓕)) := by
    refine Integrable.of_bound ?_ (M * (max C 0 * B)) (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hTh.cont.comp continuous_fst).mul (((hw.om_cont Φ hΦ 0).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).mul
          (hG.2.1.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_mul, norm_mul]
      exact mul_le_mul (hThb p.1) (hnorm p.1 p.2) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM0
  have hH : Integrable (fun p : flagN d × GA D W =>
      ∑' y : Orb W x₀, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1)
      ((vN.ν.restrict vN.𝓝).prod (vW.μ.restrict vW.𝓕)) := by
    refine Integrable.of_bound ?_ (M * (max C 0 * B)) (Filter.Eventually.of_forall fun p => ?_)
    · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (Orb W x₀)))
        (f := fun s p => ∑ y ∈ s, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1) (fun s => ?_)
        (Filter.Eventually.of_forall fun p => ?_)
      · exact (continuous_finsetSum _ fun y _ => ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul
          (((hT Φ hΦ).2.2.2.1 y.1).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))).aestronglyMeasurable
      · exact (((hsum p.1 p.2).summable.mul_left (Th p.1.1 * G p.2)).subtype _).hasSum
    · have h1 := enorm_tsum_le_tsum_enorm.trans (hall p.1 p.2 (Orb W x₀))
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [toReal_enorm, ENNReal.toReal_ofReal hK0] at h2
  rw [← Measure.prod_restrict]
  simp only [liftS_apply]
  calc ∫ n in vN.𝓝, Th n.1 * ∫ h in vW.𝓕, om (n.1, h) Φ 0 * G h ∂vW.μ ∂vN.ν
      = ∫ n in vN.𝓝, ∫ h in vW.𝓕, Th n.1 * (om (n.1, h) Φ 0 * G h) ∂vW.μ ∂vN.ν := by
        congr 1; funext n; exact (integral_const_mul _ _).symm
    _ = ∫ h in vW.𝓕, ∫ n in vN.𝓝, Th n.1 * (om (n.1, h) Φ 0 * G h) ∂vN.ν ∂vW.μ :=
        integral_integral_swap hF
    _ = ∫ h in vW.𝓕, G h * ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) (om (1, h) Φ) 0 ∂vN.ν ∂vW.μ := by
        congr 1; funext h; rw [← integral_const_mul]; congr 1; funext n; rw [hsplit]; ring
    _ = ∫ h in vW.𝓕, G h * ∫ n in vN.𝓝, ∑' x : Orb W x₀,
          Th n.1 * term ψ d W vS (om (n.1, 1) (om (1, h) Φ)) x.1 ∂vN.ν ∂vW.μ := by
        congr 1; funext h
        rw [GlobalTheory.T.thetaKernel_mean_eq_orbit_sum_mean D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh _ (hw.om_pres _ _ hΦ)]
    _ = ∫ h in vW.𝓕, ∫ n in vN.𝓝, ∑' y : Orb W x₀,
          Th n.1 * G h * term ψ d W vS (om (n.1, h) Φ) y.1 ∂vN.ν ∂vW.μ := by
        congr 1; funext h; rw [← integral_const_mul]; congr 1; funext n
        rw [← tsum_mul_left, ← hsplit]; congr 1; funext x; ring
    _ = _ := (integral_prod_symm _ hH).symm

end GlobalTheory.Unf
