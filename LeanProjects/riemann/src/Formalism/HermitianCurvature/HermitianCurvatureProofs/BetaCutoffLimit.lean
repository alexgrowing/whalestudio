import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

open MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section beta

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem JF_cutF (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (g : Mat k r) :
    JF D (Formalism.FourierDecayAlt.D.cutF D χ F ε) g = ((χ (Gf k r D.z D.z' g / ε) : ℝ) : ℂ) • JF D F g := by
  unfold JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := Formalism.FourierDecayAlt.P.B5.ae_inSS D
  filter_upwards [hae] with p hp
  have e := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g
  simp only [sgs] at e
  simp only [Formalism.FourierDecayAlt.D.cutF, e]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem hsVec_smul' [FiniteDimensional ℂ Wq] (a : ℂ) (A : Wq →L[ℂ] Wp) : hsVec (a • A) = a • hsVec A := by
  unfold hsVec; ext i; simp

theorem hsVec_cont' [FiniteDimensional ℂ Wq] : Continuous (hsVec : (Wq →L[ℂ] Wp) → _) := by
  unfold hsVec
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)

theorem inner_self_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem bcWeight_nonneg' (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _)
      (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem beta_cutF [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) =
      ∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 *
        ‖hsVec (JF D F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
  unfold beta betaBig
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [gq]
  rw [JF_cutF, hsVec_smul', inner_smul_left, inner_smul_right, inner_self_real, Complex.conj_ofReal]
  push_cast
  ring

theorem cut_bound {χ : ℝ → ℝ} (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |χ x| ≤ M := by
  obtain ⟨hs, ⟨δ, _, h0⟩, h1⟩ := hχ
  have hc : Continuous χ := hs.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x < δ
  · rw [h0 x hx, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  by_cases hx1 : 1 ≤ x
  · rw [h1 x hx1, abs_one]; exact le_max_right _ _
  · have := hM x ⟨not_lt.1 hx, le_of_not_ge hx1⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

end beta

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_cut_limit (D : RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (hχ : Formalism.FourierDecayAlt.C6.IsCut0 χ)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (hA : AB k r ≤ A) (hF : ∀ m : ℕ, InCC A m F) :
    normSq D F ≠ ⊤ ∧
      Tendsto (fun ε => beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((normSq D F).toReal : ℝ) : ℂ)) := by

  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D A hA
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin : normSq D F ≠ ⊤ := (hC0 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  refine ⟨hfin, ?_⟩
  set w : (Fin r → ℂ) × ℂ → ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') with hw
  set J : (Fin r → ℂ) × ℂ → _ := fun q => hsVec (JF D F (gq D q)) with hJ
  set h : (Fin r → ℂ) × ℂ → ℝ := fun q => w q * ‖J q‖ ^ 2 with hh
  set μQ : Measure ((Fin r → ℂ) × ℂ) := volume.restrict (Qset D) with hμQ
  have hw0 : ∀ q, 0 ≤ w q := fun q => bcWeight_nonneg' _ _ q
  have hh0 : ∀ q, 0 ≤ h q := fun q => mul_nonneg (hw0 q) (sq_nonneg _)
  have hwQ : ∀ q, q ∉ Qset D → w q = 0 := by
    intro q hq
    have : ¬ 0 < w q := hq
    exact le_antisymm (not_lt.1 this) (hw0 q)

  have hcont : ContinuousOn F (GV k r) := Formalism.FourierDecayAlt.P.B7.jc_cont (hF 4)
  have hJm : AEStronglyMeasurable J μQ := by
    have h1 := Formalism.FourierDecayAlt.P.B7.jc_aesm_J D hcont (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rw [e] at h1
    exact hsVec_cont'.comp_aestronglyMeasurable h1
  have hwm : Measurable w := Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _
  have hhm : AEStronglyMeasurable h μQ := hwm.aestronglyMeasurable.mul (hJm.norm.pow 2)

  have hlin : normSq D F = ∫⁻ q, ENNReal.ofReal (h q) ∂μQ := by
    show (∫⁻ q, ENNReal.ofReal (h q)) = _
    rw [hμQ, setLIntegral_eq_of_support_subset]
    intro q hq
    by_contra hn
    apply hq
    simp only [hh, hwQ q hn, zero_mul, ENNReal.ofReal_zero]
  have hhi : Integrable h μQ := by
    refine ⟨hhm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hh0), ← hlin]
    exact lt_top_iff_ne_top.2 hfin
  have hlim : ∫ q, ((h q : ℝ) : ℂ) ∂μQ = (((normSq D F).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhm, ← hlin]

  obtain ⟨M, hM0, hM⟩ := cut_bound hχ
  have hχc : Continuous χ := hχ.1.continuous
  have hGc : Continuous fun x : Mt k r => Gf k r D.z D.z' (Matrix.of x) :=
    (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z').comp continuous_id
  set Fe : ℝ → (Fin r → ℂ) × ℂ → ℂ := fun ε q =>
    ((w q * χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 * ‖J q‖ ^ 2 : ℝ) : ℂ) with hFe
  have hbeta : ∀ ε, beta D (Formalism.FourierDecayAlt.D.cutF D χ F ε) (Formalism.FourierDecayAlt.D.cutF D χ F ε) = ∫ q, Fe ε q ∂μQ := by
    intro ε
    rw [beta_cutF, hμQ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro q hq
    simp only [hFe, hwQ q hq, zero_mul, Complex.ofReal_zero]
  simp_rw [hbeta]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun q => M ^ 2 * h q) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    have hχm : AEStronglyMeasurable (fun q => χ (Gf k r D.z D.z' (gq D q) / ε)) μQ := by
      refine (((hχc.comp (hGc.div_const ε)).measurable.comp
        (Formalism.FourierDecayAlt.P.B7.measurable_gqM D)).aestronglyMeasurable).congr ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
      simp only [Function.comp_apply]
      rw [Formalism.FourierDecayAlt.P.B7.gqM_eq D hq]
      rfl
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hwm.aestronglyMeasurable.mul (hχm.pow 2)).mul (hJm.norm.pow 2))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun q => ?_
    simp only [hFe, Complex.norm_real, Real.norm_eq_abs]
    have h2 : χ (Gf k r D.z D.z' (gq D q) / ε) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 q) (sq_nonneg _)) (sq_nonneg _))]
    simp only [hh]
    nlinarith [hw0 q, sq_nonneg ‖J q‖, mul_nonneg (hw0 q) (sq_nonneg ‖J q‖)]
  · exact hhi.const_mul _
  · filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict D] with q hq
    have hG : 0 < Gf k r D.z D.z' (gq D q) := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq).2.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds hG)] with ε hε hle
    simp only [hFe, hh]
    rw [hχ.2.2 _ ((one_le_div (Set.mem_Ioi.mp hε)).mpr hle)]
    push_cast
    ring

end core

theorem AB_le_of_thr (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (h : 1 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    AB k r ≤ A₀ := by
  unfold AB
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set x : ℝ := (r : ℝ) + 1 with hx
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (k : ℝ) + r ≤ n := by rw [hn]; linarith
  have h2 : 1 ≤ x := by rw [hx]; linarith
  have h3 : 3 ≤ n := by rw [hn]; linarith
  have h4 : x ≤ x ^ 4 := by
    have : 1 ≤ x ^ 3 := one_le_pow₀ h2
    nlinarith
  have h5 : 2 * n + 1 ≤ n ^ 3 := by nlinarith
  have h6 : 0 ≤ (N : ℝ) * n ^ 2 := mul_nonneg hN (sq_nonneg _)
  calc 2 * ((k : ℝ) + r) * x + 1 ≤ 2 * n * x + 1 := by nlinarith
    _ ≤ x * (2 * n + 1) := by nlinarith
    _ ≤ x * n ^ 3 := by nlinarith
    _ ≤ x ^ 4 * n ^ 3 := by nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 3]
    _ ≤ 1 * x ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 4]
    _ ≤ A₀ := h

end Formalism.FourierDecayAlt.P.JCTx2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem beta_cutoff_limit : Formalism.FourierDecayAlt.JCT.BetaCutLimit := by
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP v
  obtain ⟨_, _, _, hB, _, _, _, _, _, _, hk, hA, _⟩ := hP
  exact Formalism.FourierDecayAlt.P.JCTx2.beta_cut_limit (T v).base χ hB.1 (f v) A₀
    (Formalism.FourierDecayAlt.P.JCTx2.AB_le_of_thr S.G.k S.G.r S.Ntop A₀ hk hA) (fun m => (hB.2 v).2.2.2.2.1 m)

end Formalism.FourierDecayAlt.P
