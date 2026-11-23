import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology Pointwise

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem lintegral_translate (hψ : IsStdChar D ψ (-1)) {φ : WO S T → ℂ} (hφ : IsThetaFunO ψ S T φ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hm : IsCovolOne (ratL T S) μ 𝓕) (y : WO S T) :
    ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨-, hN⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  obtain ⟨N, hN⟩ := hN φ hφ.cont (theta_norm_periodic hψ hφ)
  have hμ := hm.1
  have hs : IsAddFundamentalDomain (ratL T S) ((fun w => -y + w) ⁻¹' 𝓕) μ :=
    hm.2.1.preimage_of_equiv (measurePreserving_add_left μ (-y)).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ x => by
        change -y + (γ + x) = γ + (-y + x)
        abel
  have e1 := (measurePreserving_add_left μ y).setLIntegral_comp_preimage_emb (measurableEmbedding_addLeft y)
    (fun w => ‖φ w‖ₑ ^ 2) ((fun w => -y + w) ⁻¹' 𝓕)
  have e2 : (fun a => y + a) ⁻¹' ((fun w => -y + w) ⁻¹' 𝓕) = 𝓕 := by
    ext a
    simp
  rw [e2] at e1
  rw [e1, (hN μ _ hμ hs).2.2.1, (hN μ 𝓕 hμ hm.2.1).2.2.1, measure_preimage_add]

theorem cube_dilate_bound_at (hψ : IsStdChar D ψ (-1)) (hc : Chart θ σ) {N : ℕ} (b : Module.Basis (Fin N) ℝ (RW T S))
    {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ φ, IsThetaFunO ψ S T φ → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) φ = φ) → ∀ y : WO S T,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖φ (y + ∑ i, iotaW σ T S (t i • n • b i))‖ ^ 2 ≤ c * (l2O μ 𝓕 φ).toReal ^ 2 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ₀, 𝓕₀, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ι : (Fin N → ℝ) →+ WA T S := (iotaW σ T S).comp b.equivFun.symm.toLinearMap.toAddMonoidHom
  let π : WA T S →+ (Fin N → ℝ) := b.equivFun.toLinearMap.toAddMonoidHom.comp (piW θ T S)
  have hι : Continuous ι := (hc.continuous_iota T S).comp b.equivFunL.symm.continuous
  have hπ : Continuous π := b.equivFunL.continuous.comp (continuous_pi' hc.inf T S)
  have hπι : ∀ t, π (ι t) = t := fun t => by
    show b.equivFun (piW θ T S (iotaW σ T S (b.equivFun.symm t))) = t
    rw [hc.pi_iota, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ w, ι (π w) = iotaW σ T S (piW θ T S w) := fun w => by
    show iotaW σ T S (b.equivFun.symm (b.equivFun (piW θ T S w))) = _
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨c, K₁, hK₁, hreal⟩ := lintegral_real_le (G := WA T S) μ₀ ι π hι hπ hπι hK₀ h0
    (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := lintegral_compact_le (G := WA T S) (ratL T S) μ₀ h𝓕 hK₁
  refine ⟨c * M, fun μ 𝓕 hm n hn φ hφ hl y => ?_⟩
  obtain ⟨e, he, heL⟩ := exists_dilation (S := S) (T := T) hn
  have hsum : ∀ t : Fin N → ℝ, y + ∑ i, iotaW σ T S (t i • n • b i) = y + e (ι t) := fun t => by
    rw [he]
    show _ = y + n • iotaW σ T S (b.equivFun.symm t)
    rw [Module.Basis.equivFun_symm_apply, ← map_nsmul, Finset.smul_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm]
  have en : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hmeas : Measurable fun w : WA T S => ‖φ (y + e w)‖ₑ ^ 2 :=
    (hφ.cont.comp (continuous_const.add e.continuous)).measurable.enorm.pow_const 2
  have a1 := hreal _ hmeas fun w hw => by
    have hinf : (w - ι (π w)).map (infPart D) = 0 := by
      have hp : piW θ T S (w - ι (π w)) = 0 := by rw [hιπ, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
      ext i j
      exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
    have := GlobalTheory.HeisOrtho.norm_heisO hψ.1 φ (n • (w - ι (π w))) (y + e (ι (π w)))
    rw [hl _ hw hinf, ← he, add_assoc, ← map_add, add_sub_cancel] at this
    rw [← en, ← en, this]
  have a2 := hM _ hmeas fun γ hγ w => by
    rw [← en, ← en, map_add, add_left_comm, theta_norm_periodic hψ hφ _ ((heL γ).2 hγ)]
  have a3 : ∫⁻ w in 𝓕₀, ‖φ (y + e w)‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ :=
    lintegral_comp_aut (G := WA T S) (ratL T S) hK hcov e heL hμ h𝓕 h1 hm.1 hm.2.1 hm.2.2
      (f := fun x => φ (y + x)) (hφ.cont.comp (continuous_const.add continuous_id)) fun γ hγ w => by
        change ‖φ (y + (γ + w))‖ = ‖φ (y + w)‖
        rw [add_left_comm]
        exact theta_norm_periodic hψ hφ γ hγ _
  have a3' := lintegral_translate hψ hφ hm y
  simp only [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + e (ι t))‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    ((hφ.cont.comp (continuous_const.add (e.continuous.comp hι))).norm.pow 2).aestronglyMeasurable]
  simp only [en]
  have a4 := a1.trans (mul_le_mul_right (a2.trans_eq (congrArg _ ((a3.trans a3').trans (l2O_sq_eq_lintegral μ 𝓕 φ).symm))) _)
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    (ENNReal.pow_ne_top (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hm.1 hm.2.1 hφ)))) a4).trans_eq ?_
  simp [mul_assoc]

end GlobalTheory.SupremumSobolevWords

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.Size

end GlobalTheory.SupremumSobolevWords

end
