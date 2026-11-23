import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaLawTendstoUniformNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergAverageCompactSymplecticTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergAverageRealPlacesSmoothStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisSmoothing

open GlobalTheory.FockCompare

theorem norm_integral_sub_le {X : Type} [MeasurableSpace X] (μ : Measure X) (φ : X → ℝ) (F : X → ℂ) (c : ℂ) (δ : ℝ)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∫ x, φ x ∂μ = 1) (hφ : Integrable φ μ) (hF : Integrable (fun x => (φ x : ℂ) * F x) μ)
    (hb : ∀ x, φ x ≠ 0 → ‖F x - c‖ ≤ δ) : ‖∫ x, (φ x : ℂ) * F x ∂μ - c‖ ≤ δ := by
  have hc : Integrable (fun x => (φ x : ℂ) * c) μ := hφ.ofReal.mul_const c
  have e : ∫ x, (φ x : ℂ) * c ∂μ = c := by
    rw [integral_mul_const, integral_complex_ofReal, h1]
    simp
  have e2 : ∫ x, φ x * δ ∂μ = δ := by rw [integral_mul_const, h1, one_mul]
  rw [← e2]
  conv_lhs => rw [← e, ← integral_sub hF hc]
  refine norm_integral_le_of_norm_le (hφ.mul_const δ) (Filter.Eventually.of_forall fun x => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x)]
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hb x hx) (h0 x)

theorem isAddHaarMeasure_volume (ι m n : Type) [Fintype ι] [Fintype m] [Fintype n] :
    (volume : Measure (ι → m → n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (m → n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem exists_theta_of_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (f : WO A T → ℂ), Continuous f → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), f (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * f u) → (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u f = f) → ∀ N ∈ 𝓝 (0 : WO A T), ∀ δ : ℝ, (∀ a ∈ N, ∀ w, ‖heisO ψ A T a f w - f w‖ ≤ δ) → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ w, ‖g w - f w‖ ≤ δ := by
  intro D ψ hψ A T f hf hlaw hlev N hN δ hδ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -⟩ := lattice_Mx D T.rank A.rank
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := isAddHaarMeasure_volume _ _ _
  have hι : Continuous (iotaW σ T A) := h.continuous_iota T A
  have hN' : iotaW σ T A ⁻¹' N ∈ 𝓝 (0 : RW T A) :=
    hι.continuousAt.preimage_mem_nhds (by rw [AddMonoidHom.map_zero]; exact hN)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN'
  let b : ContDiffBump (0 : RW T A) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let φ : RW T A → ℝ := b.normed volume
  have hφs : ContDiff ℝ ∞ φ := b.contDiff_normed
  have hφc : HasCompactSupport φ := b.hasCompactSupport_normed
  let g : WO A T → ℂ := fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
  have hsm : Sm (iotaW σ T A) g := GlobalTheory.T.heisenbergAverage_realPlaces_smooth D θ σ h ψ hψ A T φ hφs hφc f hf
  have hl : ∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ A T u g = g := by
    obtain ⟨U, hU, hUf⟩ := hlev
    refine ⟨U, hU, fun u hu h0 => funext fun w => ?_⟩
    show ψ (symplOH A T w u) * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (w + u) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e := congrFun (GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (h.real_iota T A x) (hUf u hu h0)) w
    show _ = (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← e]
    exact mul_left_comm _ _ _
  refine ⟨g, ⟨fun γ w => ?_, hl, GlobalTheory.OrientedHeis.continuous_of_level h hψ.1.1 g hl hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T A).1 g).2 hsm⟩, fun w => ?_⟩
  · show ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) =
      _ * ∫ x, (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (φ x : ℂ) * heisO ψ A T (iotaW σ T A x) f (ratW T A γ + w) = _
    rw [GlobalTheory.OrientedHeis.heisO_quasi _ f hlaw]
    exact mul_left_comm _ _ _
  · have hc : Continuous fun x : RW T A => heisO ψ A T (iotaW σ T A x) f w :=
      (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_const hι)).mul
        (hf.comp (continuous_const.add hι))
    have hφℂ : HasCompactSupport fun x => (φ x : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
    refine norm_integral_sub_le volume φ _ (f w) δ b.nonneg_normed b.integral_normed b.integrable_normed
      (((Complex.continuous_ofReal.comp hφs.continuous).mul hc).integrable_of_hasCompactSupport hφℂ.mul_right)
      fun x hx => hδ _ (hrN ?_) w
    have : x ∈ Function.support φ := hx
    rwa [b.support_normed_eq] at this

theorem exists_theta_near : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ g : WO A T → ℂ, IsThetaFunO ψ A T g ∧ ∀ u, ‖q u - g u‖ ≤ ε := by
  have h1 := GlobalTheory.T.heisenbergOperator_thetaLaw_tendsto_uniform_near_zero
  have h2a := GlobalTheory.T.exists_small_compact_level_symplecticCharacter_trivial
  have h2b := GlobalTheory.T.exists_heisenbergAverage_compactSymplecticTrivial
  have h4 := exists_theta_of_level
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨N, hN, hNq⟩ := h1 D ψ hψ A T q hq hlaw (ε / 2) (half_pos hε)
  obtain ⟨K, hKc, hKN, -, ⟨U, hU, hUK⟩, hKψ⟩ := h2a D ψ hψ A T N hN
  obtain ⟨g1, hg1c, hg1law, hg1K, hg1near⟩ := h2b D ψ hψ A T K hKc hKψ q hq hlaw
  have hg1q : ∀ w, ‖g1 w - q w‖ ≤ ε / 2 := hg1near (ε / 2) (fun a ha w => hNq a (hKN ha) w)
  obtain ⟨N2, hN2, hN2g⟩ := h1 D ψ hψ A T g1 hg1c hg1law (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgg1⟩ := h4 D ψ hψ A T g1 hg1c hg1law ⟨U, hU, fun u hu h0 => hg1K u (hUK u hu h0)⟩ N2 hN2 (ε / 2) hN2g
  refine ⟨g, hg, fun w => ?_⟩
  have e : q w - g w = (g1 w - g w) - (g1 w - q w) := by ring
  rw [e]
  calc ‖(g1 w - g w) - (g1 w - q w)‖ ≤ ‖g1 w - g w‖ + ‖g1 w - q w‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [norm_sub_rev]; exact hgg1 w
        · exact hg1q w
    _ = ε := add_halves ε

end GlobalTheory.HeisSmoothing

end
