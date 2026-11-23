import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroupsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PoinCusp

theorem poin_isCuspFun : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hP D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := GlobalTheory.T.exists_closed_parabolic_subgroups hP D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).1) (fun τ => (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

end GlobalTheory.PoinCusp
