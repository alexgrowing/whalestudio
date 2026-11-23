import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Inj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL_alt : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem R_apply_eq {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {U : Subgroup (GL (Fin a) (Af E))}
    {v : L2 (latticeGL E a) μ} (hv : ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) {g : GA E a}
    (hu : GeneralLinearGroup.map (pFin E) g⁻¹ ∈ U) :
    R (latticeGL E a) μ g v = R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v := by
  have e : g = infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹ * finGL E a (GeneralLinearGroup.map (pFin E) g⁻¹)⁻¹ := by
    rw [map_inv (infGL E a), map_inv (finGL E a), ← _root_.mul_inv_rev, ← infGL_comm, infGL_mul_finGL, inv_inv]
  conv_lhs => rw [e]
  rw [map_mul, ContinuousLinearMap.mul_apply, hv _ (U.inv_mem hu)]

theorem exists_isTest_Rop_injective : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  intro E _ _ _ a μ _ _ U hU hUc X hX hfix
  let Φ : GL (Fin a) (Cinf E) → (X →L[ℂ] L2 (latticeGL E a) μ) := fun y =>
    (R (latticeGL E a) μ (infGL E a y⁻¹) - ContinuousLinearMap.id ℂ _) ∘L X.subtypeL
  have hΦv : ∀ y (w : X), Φ y w = R (latticeGL E a) μ (infGL E a y⁻¹) w - w := fun _ _ => rfl
  have hΦ : Continuous Φ := by
    refine continuous_clm_apply.2 fun w => ?_
    simp only [hΦv]
    exact ((continuous_R (w : L2 (latticeGL E a) μ)).comp (continuous_infGL_alt.comp continuous_inv)).sub
      continuous_const
  have hΦ1 : Φ 1 = 0 := by
    ext w
    simp [hΦv]
  have hN : {y | ‖Φ y‖ ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) := by
    have h1 : Metric.closedBall (0 : X →L[ℂ] L2 (latticeGL E a) μ) (1 / 2) ∈ 𝓝 (Φ 1) := by
      rw [hΦ1]; exact Metric.closedBall_mem_nhds _ (by norm_num)
    have h2 := hΦ.continuousAt.preimage_mem_nhds h1
    simpa [Metric.closedBall, dist_zero_right] using h2
  obtain ⟨β₀, h0, hpos, htest, hconj, hsupp⟩ := GlobalTheory.T.exists_nonneg_test_function_near_one E a _ hN
  refine ⟨fun x => (β₀ x : ℂ), htest, hconj, fun v hv hRv => ?_⟩
  obtain ⟨hc, hcs⟩ := GlobalTheory.T.test_function_continuous_compact_support E a U hU hUc _ htest
  set f := tst U (fun x => (β₀ x : ℂ)) with hf
  set fr : GA E a → ℝ := fun g => (f g).re with hfr
  have hf_eq : ∀ g, f g = (fr g : ℂ) := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs <;> simp
  have hfr0 : ∀ g, 0 ≤ fr g := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs
    · simpa using h0 _
    · simp
  have hfrc : Continuous fr := Complex.continuous_re.comp hc
  have hfrs : HasCompactSupport fr := hcs.comp_left Complex.zero_re
  have hfr1 : fr 1 ≠ 0 := by
    have : fr 1 = β₀ (oneL E a) := by
      simp [hfr, hf, tst, ker, U.one_mem]
    rw [this]; exact hpos.ne'
  have hIpos : 0 < ∫ g, fr g ∂μ :=
    hfrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hfrs hfr0 hfr1
  have hint : Integrable f μ := hc.integrable_of_hasCompactSupport hcs
  have hfrint : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hrep := (isRepOp_Rop (Γ := latticeGL E a) (μ := μ) hint) v
  have key : (∫ g, f g ∂μ) • v = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
    calc (∫ g, f g ∂μ) • v = (∫ g, f g ∂μ) • v - ∫ g, f g • R (latticeGL E a) μ g v ∂μ := by
          have h2 := hrep.2.symm.trans hRv
          rw [show (∫ g, f g • R (latticeGL E a) μ g v ∂μ) = 0 from h2, sub_zero]
      _ = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
          rw [← integral_smul_const, ← integral_sub (hint.smul_const v) hrep.1]
          simp_rw [smul_sub]
  have hI : (∫ g, f g ∂μ) = ((∫ g, fr g ∂μ : ℝ) : ℂ) := by
    simp_rw [hf_eq]; exact integral_ofReal
  have hpt : ∀ g, fr g ≠ 0 → ‖v - R (latticeGL E a) μ g v‖ ≤ ‖v‖ / 2 := by
    intro g hg
    have hfg : f g ≠ 0 := fun h => hg (by show (f g).re = 0; rw [h]; simp)
    simp only [hf, tst, ker] at hfg
    split_ifs at hfg with hu
    · have hb : β₀ (toL (GeneralLinearGroup.map (pInf E) g⁻¹).val) ≠ 0 := by
        intro h; apply hfg; simp only [Complex.ofReal_eq_zero]; convert h using 1
      obtain ⟨y, hyN, hy⟩ := hsupp _ hb
      have hy' : y = GeneralLinearGroup.map (pInf E) g⁻¹ := Units.ext (Matrix.of.symm.injective hy)
      rw [R_apply_eq (fun u hu' => hfix u hu' v hv) hu, norm_sub_rev]
      calc ‖R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v - v‖
          = ‖Φ y ⟨v, hv⟩‖ := by rw [hΦv, hy']
        _ ≤ ‖Φ y‖ * ‖(⟨v, hv⟩ : X)‖ := (Φ y).le_opNorm _
        _ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hyN (norm_nonneg _)
        _ = ‖v‖ / 2 := by ring
    · exact absurd rfl hfg
  have hbound : ‖∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ‖ ≤ ∫ g, fr g * (‖v‖ / 2) ∂μ :=
    norm_integral_le_of_norm_le (hfrint.mul_const _) (Filter.Eventually.of_forall fun g => by
      rw [norm_smul, hf_eq, Complex.norm_real, Real.norm_of_nonneg (hfr0 g)]
      by_cases hg : fr g = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (hpt g hg) (hfr0 g))
  rw [integral_mul_const, ← key, hI, norm_smul, Complex.norm_real, Real.norm_of_nonneg hIpos.le] at hbound
  have hle : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 hle

end GlobalTheory.CompanionTheory.SmoothRep.Inj
