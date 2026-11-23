import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtLogMinorProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPhlaBound
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory.Up GlobalTheory.PoleDbar GlobalTheory.Up.OrbitInterpolation

namespace GlobalTheory.CentreCusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem poleSolve' (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E))
    (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (κ ε C bb m : ℝ) (h0 : IsOrth X x0)
    (hla : ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ε → -phla X la (cpt X x0 z) ≤ A) (hε : 0 < ε) (hbb : 0 ≤ bb)
    (hm : bb + κ < m)
    (hL : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ) :
    ∃ (χ : ℝ → ℝ) (M : ℝ≥0∞), Continuous χ ∧ (∀ u ≤ ε / 2, χ u = 1) ∧ (∀ u, ε ≤ u → χ u = 0) ∧ (∀ u, |χ u| ≤ 1) ∧ M < ⊤ ∧
    ∀ δ ψ, IsPole X G x0 κ ε C δ ψ → ∃ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) ∧
      ∫⁻ z, ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
        Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) ∂muF X x0 ≤ M := by
  obtain ⟨χ, D, hχ, h1, h2, h3, hD, hd⟩ := exists_cutoff hε
  obtain ⟨A, hA⟩ := hla
  have hU := OntoB.isOpen_OmF X x0
  have hD0 : 0 ≤ D := (sq_nonneg _).trans (hD 0)
  set R : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hc : 0 < m - κ - bb := by linarith
  set K : ℝ := D * R / (m - κ - bb) with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set (V (nd X)) := rhF X x0 ⁻¹' Set.Icc (ε / 2) ε with hS
  have hSm : MeasurableSet S := measurable_rhF X x0 measurableSet_Icc
  have hfin : muF X x0 S < ⊤ :=
    (measure_mono fun z hz => hz.2).trans_lt (SublevelFin.muF_sublevel_lt_top hI r X x0 h0 ε)
  refine ⟨χ, ENNReal.ofReal (K * Real.exp (A + C + bb * ε)) * muF X x0 S, hχ.continuous, h1, h2, h3,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin, fun δ ψ hψ => ?_⟩
  obtain ⟨hψs, hψl⟩ := hψ.2.2.1 x0 h0
  set φ : V (nd X) → ℝ := fun z => (phla X la (cpt X x0 z) + ψ (cpt X x0 z)) +
    ((-1) * Real.log (densF X x0 z) + (-bb) * rhF X x0 z) with hφ
  have s1 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => phla X la (cpt X x0 w)) z :=
    fun z hz => IW.phla_cpt_cdAt X x0 hz la
  have s2 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => ψ (cpt X x0 w)) z :=
    fun z hz => hψs.contDiffAt (hU.mem_nhds hz)
  have s3 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z :=
    fun z hz => OntoB.logDens_contDiffAt hz
  have s4 : ∀ z ∈ OmF X x0, ContDiffAt ℝ ∞ (rhF X x0) z := fun z hz => OntoB.rhF_contDiffAt hz
  have hφl : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, (m - κ - bb) * leviRh X x0 z ξ ≤
      (leviV (nd X) (fun w => ((φ w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ
    have t1 := (s1 z hz).of_le HE.two_le_inf
    have t2 := (s2 z hz).of_le HE.two_le_inf
    have t3 := (s3 z hz).of_le HE.two_le_inf
    have t4 := (s4 z hz).of_le HE.two_le_inf
    have a1 := hL z hz ξ
    have a2 := hψl z hz ξ
    simp only [hφ]
    rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add (t1.add t2) ((contDiffAt_const.mul t3).add (contDiffAt_const.mul t4)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add t1 t2,
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul t3) (contDiffAt_const.mul t4),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ t3, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ t4]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    unfold leviO leviM leviDens at *
    unfold leviRh at *
    linarith
  have hexp : ∀ z ∈ OmF X x0, Real.exp (-φ z) = densF X x0 z *
      (Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) := by
    intro z hz
    unfold kaF
    rw [← Real.exp_sub]
    conv_rhs => rw [← Real.exp_log (OntoB.densF_pos hz), ← Real.exp_add]
    congr 1
    simp only [hφ]
    ring
  obtain ⟨F, hF, hest⟩ := HE.hormander_open hU (eF X x0)
    (fun z hz => (ExF.eF_contDiffAt X x0 h0 hz).contDiffWithinAt) (levi_eF_nonneg X h0)
    (ExF.isCompact_subF X x0 h0) φ
    (fun z hz => (((s1 z hz).add (s2 z hz)).add ((contDiffAt_const.mul (s3 z hz)).add
      (contDiffAt_const.mul (s4 z hz)))).contDiffWithinAt)
    (fun z hz ξ => (mul_nonneg hc.le (Up.leviRh_nonneg h0 hz ξ)).trans (hφl z hz ξ))
    (fun z => ((χ (rhF X x0 z) : ℝ) : ℂ))
    (fun z hz => (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (hχ.contDiffAt.comp z (s4 z hz))).contDiffWithinAt)
    (S.indicator fun _ => ENNReal.ofReal K) (measurable_const.indicator hSm) (fun z hz ξ => by
      have hrd : DifferentiableAt ℝ (rhF X x0) z := (s4 z hz).differentiableAt (by simp)
      have hcd : DifferentiableAt ℝ χ (rhF X x0 z) := hχ.differentiable (by simp) _
      have e : ‖∑ j, wdb (nd X) j (fun z => ((χ (rhF X x0 z) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 =
          deriv χ (rhF X x0 z) ^ 2 * Complex.normSq
            (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) := by
        simp only [wdb_ofReal_comp hcd hrd, wdb_ofReal hrd, mul_assoc, ← map_mul]
        rw [← Finset.mul_sum, ← map_sum, norm_mul, Complex.norm_conj, mul_pow,
          Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [e]
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, ← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        have g1 : _ ≤ R * leviRh X x0 z ξ := RhGradFStatement_holds r X x0 h0 z hz ξ
        refine (mul_le_mul (hD _) g1 (Complex.normSq_nonneg _) hD0).trans ?_
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hφl z hz ξ) hK0)
        rw [hK]
        field_simp
      · rw [hd _ hzS]
        simp)
  refine ⟨F, hF, ?_⟩
  rw [lintegral_muF]
  refine le_trans (le_of_eq ?_) (hest.trans ?_)
  · refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
    rw [hexp z hz, ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]
    congr 1
    ring
  · rw [← lintegral_indicator_const hSm, lintegral_muF]
    refine setLIntegral_mono' hU.measurableSet fun z hz => ?_
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, hexp z hz, ← ENNReal.ofReal_mul hK0,
        ← ENNReal.ofReal_mul (OntoB.densF_pos hz).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) (OntoB.densF_pos hz).le
      unfold kaF
      rw [← Real.exp_sub]
      refine Real.exp_le_exp.2 ?_
      have b1 := hA z hz hzS.2
      have b2 := hψ.2.2.2.2 _ hz (by rw [Up.rhX_cpt h0 hz]; exact hzS.1)
        (by rw [Up.rhX_cpt h0 hz]; exact hzS.2)
      have b3 := mul_le_mul_of_nonneg_left hzS.2 hbb
      linarith
    · rw [Set.indicator_of_notMem hzS, zero_mul]
      exact zero_le

theorem lintegral_lt_top' (hMI : MeasInvStatement (E := E)) {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
    (h0 : IsOrth X x0) {la : Wt X.Ψ r} {bb ε : ℝ}
    (hla : ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ε → -phla X la (cpt X x0 z) ≤ A) (hbb : 0 ≤ bb)
    {χ : ℝ → ℝ} (hχ0 : ∀ u, ε ≤ u → χ u = 0) (hχ1 : ∀ u, |χ u| ≤ 1) {ψ : Frame X.Ψ r → ℝ}
    (hψ : ∀ x ∈ X.dom, ψ x ≤ 0) {F : V (nd X) → ℂ}
    (hfin : ∫⁻ z, ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
        Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) ∂muF X x0 < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z)
      ∂muF X x0 < ⊤ := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ε → Real.exp (-phla X la (cpt X x0 z)) ≤ K :=
    hla.elim fun A hA => ⟨Real.exp A, fun z hz h => Real.exp_le_exp.2 (hA z hz h)⟩
  set S : Set (Frame X.Ψ r) := {y | rhX X x0 y ≤ ε} with hS
  have hSm : MeasurableSet (cpt X x0 ⁻¹' S) :=
    (OntoB.cd_cpt X x0).continuous.measurable (measurableSet_le (measurable_rhX h0) measurable_const)
  have hSμ : muF X x0 (cpt X x0 ⁻¹' S) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono_ae ?_) (SublevelFin.muF_sublevel_lt_top hMI r X x0 h0 ε)
    filter_upwards [ae_mem_OmF X x0] with z hz h
    have h' : rhX X x0 (cpt X x0 z) ≤ ε := h
    rw [rhX_cpt h0 hz] at h'
    exact h'
  have hae : ∀ᵐ z ∂muF X x0,
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z) ≤
      (cpt X x0 ⁻¹' S).indicator (fun _ => ENNReal.ofReal (2 * (K * Real.exp (bb * ε)))) z +
        ENNReal.ofReal 2 * ENNReal.ofReal (‖(χ (rhF X x0 z) : ℂ) - F z‖ ^ 2 *
          Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z) := by
    filter_upwards [ae_mem_OmF X x0] with z hz
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    set w := Real.exp (-phla X la (cpt X x0 z)) / kaF X x0 bb z with hw
    set w' := Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hw'
    have hw0 : 0 < w := div_pos (Real.exp_pos _) hk
    have hww : w ≤ w' := div_le_div_of_nonneg_right
      (Real.exp_le_exp.2 (by linarith [hψ _ hz])) hk.le
    set c : ℂ := (χ (rhF X x0 z) : ℂ) with hc
    have h1 : ENNReal.ofReal (2 * (‖c‖ ^ 2 * w)) ≤
        (cpt X x0 ⁻¹' S).indicator (fun _ => ENNReal.ofReal (2 * (K * Real.exp (bb * ε)))) z := by
      by_cases hzS : rhF X x0 z ≤ ε
      · have hm : z ∈ cpt X x0 ⁻¹' S := by
          show rhX X x0 (cpt X x0 z) ≤ ε
          rwa [rhX_cpt h0 hz]
        rw [Set.indicator_of_mem hm]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ two_pos.le)
        have c1 : ‖c‖ ^ 2 ≤ 1 := by
          rw [hc, Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hχ1 _)
        refine (mul_le_of_le_one_left hw0.le c1).trans ?_
        rw [hw, div_eq_mul_inv, kaF, ← Real.exp_neg]
        refine mul_le_mul (hK z hz hzS) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
          ((Real.exp_pos _).le.trans (hK z hz hzS))
        nlinarith [mul_le_mul_of_nonneg_left hzS hbb]
      · simp [hc, hχ0 _ (not_le.1 hzS).le]
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * ‖c - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖c‖ + ‖c - F z‖ := by simpa using norm_sub_le c (c - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg c, norm_nonneg (c - F z), sq_nonneg (‖c‖ - ‖c - F z‖)]
    rw [← ENNReal.ofReal_mul two_pos.le, mul_div_assoc, mul_div_assoc, ← hw, ← hw']
    refine le_trans ?_ (add_le_add_left h1 _)
    have hw1 : 0 < w' := hw0.trans_le hww
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity) (by positivity)).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hw0.le,
      mul_le_mul_of_nonneg_left hww (sq_nonneg ‖c - F z‖)]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hSm), lintegral_indicator_const hSm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSμ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

theorem exists_approx'
    (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E))
    (hExt : ExtFStatement (E := E)) (hMI : MeasInvStatement (E := E)) (hPE : PoleEx (E := E))
    (hPP : PolePoint (E := E)) {r : ℕ} {X : Data E r}
    {G : Subgroup (GL (Fin r) E)} {x0 : Frame X.Ψ r} {la : Wt X.Ψ r} {ρ0 bb m : ℝ}
    (h0 : IsOrth X x0) (hd : 1 ≤ dimX X) (hρ0 : 0 < ρ0) (hG : FreeBall X G x0 ρ0)
    (hla : ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ρ0 → -phla X la (cpt X x0 z) ≤ A)
    (hbb : 0 ≤ bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    {κ : Frame X.Ψ r → ℝ} (hκm : Measurable κ) (hκ1 : ∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1)
    (hκB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x)
    (hκF : ∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z)
    (hloc : ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧
      InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + 0)))) bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ‖P x0 - 1‖ ≤ η ∧
      ∀ g ∈ G, g ≠ 1 → ‖P (lact g x0)‖ ≤ η * Real.sqrt (κ (lact g x0)) := by
  have hd' : (0 : ℝ) < dimX X := by exact_mod_cast hd
  have hq : 0 < (dimX X : ℝ) / ρ0 := div_pos hd' hρ0
  obtain ⟨θ, hθ1, hθ⟩ := exists_between ((one_lt_div hq).2 (by linarith : (dimX X : ℝ) / ρ0 < m - bb))
  rw [lt_div_iff₀ hq] at hθ
  obtain ⟨ε, C, hε, hερ, hψ⟩ := hPE r X G x0 ρ0 θ h0 hρ0 hθ1 hG
  have hla' : ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ε → -phla X la (cpt X x0 z) ≤ A :=
    hla.imp fun A hA z hz h => hA z hz (h.trans hερ.le)
  obtain ⟨χ, M, -, hχ1, hχ0, hχb, hM, hsol⟩ := poleSolve' hMI r X G x0 la (dimX X * θ / ρ0) ε C bb m h0 hla' hε hbb
    (by have : (dimX X : ℝ) * θ / ρ0 = θ * (dimX X / ρ0) := by ring
        linarith) hcurv
  obtain ⟨ρ, A, hρ, hA, hball⟩ := exists_ball X la (half_pos hε) (fun x hx => (hκ1 x hx).1) hloc
  set D : ℝ := Real.exp C * A * M.toReal with hD
  have hD0 : 0 ≤ D := by positivity
  set c : ℝ := η ^ 2 / (D + 1) with hc
  have hc0 : 0 < c := by positivity
  have hcD : c * D ≤ η ^ 2 := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg η]
  obtain ⟨δ0, hδ0, hpt⟩ := hPP r X ρ c hd hρ hc0
  have hδ : 0 < min δ0 1 := lt_min hδ0 one_pos
  obtain ⟨ψ, hψ⟩ := hψ (min δ0 1) hδ (min_le_right _ _)
  obtain ⟨F, hF, hFM⟩ := hsol _ ψ hψ
  have hfin := lintegral_lt_top' hMI h0 hla' hbb hχ0 hχb hψ.2.1 (hFM.trans_lt hM)
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 h0 la F hF fun K _ _ => by
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt
      (lt_of_le_of_lt (lintegral_mono_ae ?_) hfin)
    filter_upwards [ae_mem_OmF X x0] with z hz
    refine ENNReal.ofReal_le_ofReal (le_div_self (by positivity) (hka z) ?_)
    rw [← hκF z hz]; exact (hκ1 _ hz).2

  have hw : ∀ g ∈ G, ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∀ s : ℝ, 0 ≤ s →
      ENNReal.ofReal (s * (rhF X (lact g x0) z + min δ0 1) ^ (-(dimX X : ℝ))) ≤
      ENNReal.ofReal (Real.exp C * A * κ (lact g x0)) * ENNReal.ofReal (s *
        Real.exp (-(phla X la (cpt X (lact g x0) z) + ψ (cpt X (lact g x0) z))) /
          κ (cpt X (lact g x0) z)) := by
    intro g hg z hz s hs
    have h1 := isOrth_lact_of_isUStab (hG.isUStab hg) h0
    obtain ⟨hzO, hzr, hzw⟩ := hball _ h1 z (mem_ball_zero_iff.1 hz)
    have h2 := rpow_le_weight h0 hG.2.1 hδ hψ hg hzO (by linarith)
    have hk := (hκ1 _ (IW.orth_mem_dom X _ h1)).1
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ s * (Real.exp C * Real.exp (-ψ (cpt X (lact g x0) z))) := mul_le_mul_of_nonneg_left h2 hs
      _ ≤ s * (Real.exp C * Real.exp (-ψ (cpt X (lact g x0) z))) * (A * κ (lact g x0) *
          (Real.exp (-phla X la (cpt X (lact g x0) z)) / κ (cpt X (lact g x0) z))) :=
        le_mul_of_one_le_right (by positivity) hzw
      _ = _ := by rw [neg_add, Real.exp_add]; ring
  refine ⟨F, P, hF, ?_, hP, hPF, ?_, fun g hg hne => ?_⟩
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hfin
    filter_upwards [ae_mem_OmF X x0] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le), add_zero]
    congr 1
    ring
  · have hk := hκ1 _ (IW.orth_mem_dom X _ h0)
    have h1 := hpt x0 h0 _ hδ (min_le_left _ _) (fun z => 1 - F z)
      ((differentiableOn_const _).sub (hF.mono Set.inter_subset_right))
    have h2 := value_le (B := Real.exp C * A * κ x0) hc0.le (by have := hk.1; positivity) hM h1
      (fun z hz => by
        have := hw 1 G.one_mem z hz (‖1 - F z‖ ^ 2) (by positivity)
        obtain ⟨hzO, hzr, -⟩ := hball _ h0 z (mem_ball_zero_iff.1 hz)
        rw [FundSetPf.lact_one, hκF z hzO] at this
        simp only [hχ1 _ hzr, Complex.ofReal_one]
        exact this) hFM
    have h3 : P x0 = F 0 := by
      have := hPF 0 (IW.zero_mem_OmF X x0 h0)
      rwa [IW.cpt_zero] at this
    rw [h3, norm_sub_rev]
    refine abs_le_of_sq_le_sq' ?_ hη.le |>.2
    refine h2.trans (le_trans ?_ hcD)
    calc _ = c * D * κ x0 := by rw [hD]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hk.2
  · have h1 := isOrth_lact_of_isUStab (hG.isUStab hg) h0
    have hk := hκ1 _ (IW.orth_mem_dom X _ h1)
    obtain ⟨-, hW, -⟩ := KronMetric.kronMetric hN r X la ψ (hψ.isInvFn hG.1)
      (fun x hx => (hψ.2.2.1 x hx).1) ⟨0, hψ.2.1⟩
    obtain ⟨φ, hφ, hφM⟩ := exists_density hMI h0 hχ0 hκm hκB hκF hW hP hPF hFM
    have h2 := hpt _ h1 _ hδ (min_le_left _ _) (fun z => P (cpt X (lact g x0) z))
      ((OntoB.hol_comp X _ hP.1).mono Set.inter_subset_right)
    have h3 := value_le (B := Real.exp C * A * κ (lact g x0)) hc0.le (by have := hk.1; positivity) hM h2
      (fun z hz => by
        obtain ⟨hzO, hzr, -⟩ := hball _ h1 z (mem_ball_zero_iff.1 hz)
        have hg' := hG.isUStab (G.inv_mem hg)
        have h4 := hG.2.2 g hg hne _ (MajInv.lact_mem_dom X hg' hzO)
          (by rw [rhX_lact hg', inv_inv, rhX_cpt h1 hzO]; linarith)
        rw [← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one] at h4
        rw [hφ _ hzO (by linarith)]
        exact hw g hg z hz _ (by positivity)) (hφM _ h1)
    rw [IW.cpt_zero] at h3
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt hk.1.le]
    refine h3.trans ?_
    calc _ = c * D * κ (lact g x0) := by rw [hD]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcD hk.1.le

theorem orbitInterp' (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r)
    (ρ0 bb m : ℝ) (h0 : IsOrth X x0) (hd : 1 ≤ dimX X) (hρ0 : 0 < ρ0) (hG : FreeBall X G x0 ρ0)
    (hla : ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ ρ0 → -phla X la (cpt X x0 z) ≤ A)
    (hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    (hSS : ∀ P, X.IsBddSec la P → P ∈ X.SS la) :
    ∃ u0 ∈ X.SS la, u0 x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → u0 (lact γ x0) = 0 := by
  classical
  have hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E) :=
    ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
  have hPoin : PoinStatement (E := E) := poin_holds
  have hExt : ExtFStatement (E := E) := extFStatement_holds
  have hMI : MeasInvStatement (E := E) := measInv_holds
  have hPE : PoleEx (E := E) := GlobalTheory.PoleExistence.poleEx_holds
  have hPP : PolePoint (E := E) := GlobalTheory.Up.polePoint_holds
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  obtain ⟨κ, hκm, hκ1, hκB, hκF, ⟨Cs, hCs, hsum⟩, hloc⟩ :=
    GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic GlobalTheory.MinorRatioNear.minorRatio_near
      (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep) r X x0 h0 hPD bb hbb
  obtain ⟨-, hW, hWl⟩ := KronMetric.kronMetric hN r X la (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨⟨hz, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  let S : Submodule ℂ (Frame X.Ψ r → ℂ) :=
    { carrier := X.SS la
      add_mem' := fun {P Q} hP hQ => hadd P hP Q hQ
      zero_mem' := hz
      smul_mem' := fun a P hP => hsmul a P hP }
  obtain ⟨T, hT⟩ := X.Γ_index
  have hx0 := IW.orth_mem_dom X x0 h0
  obtain ⟨u, hu, hu1, hu0⟩ := exists_of_approx S x0
    (fun s : {s : T // s.1⁻¹ ∈ G ∧ s.1⁻¹ ∉ X.Γ} => lact s.1.1⁻¹ x0) fun η hη => by
    have hη' : 0 < η / (Cs.toReal + 1) := by positivity
    obtain ⟨F, P, hF, hIn, hP, hPF, hP1, hP0⟩ := exists_approx' hN hExt hMI hPE hPP h0 hd hρ0 hG hla
      hbb0 hm hcurv hκm hκ1 hκB hκF hloc hη'
    obtain ⟨hs, hbd, -⟩ := hPoin r X x0 h0 hPD la _ bb hW hWl hbb F P hF hIn hP hPF
    have hn : ∀ (γ : X.Γ) (y : Frame X.Ψ r), ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ :=
      fun γ y => by rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have he : η / (Cs.toReal + 1) + η / (Cs.toReal + 1) * Cs.toReal = η := by field_simp; ring
    refine ⟨poin X la P, hSS _ hbd, ?_, fun s => ?_⟩
    · have hs0 := hs x0 hx0
      unfold poin
      rw [hs0.of_norm.tsum_eq_add_tsum_ite 1]
      simp only [OneMemClass.coe_one, chi_one, FundSetPf.lact_one, inv_one, one_mul]
      have hle : ∀ γ : X.Γ, ‖if γ = 1 then 0 else (X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ ≤
          ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ := fun γ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hs1 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs0
      have h2 := (norm_tsum_le_tsum_norm hs1).trans (tsum_le_of_le hs1 (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          split_ifs with h
          · rw [norm_zero]; positivity
          · rw [hn]
            exact hP0 γ.1 (hG.1 γ.2) fun h' => h (Subtype.ext h')) hCs (hsum x0 hx0))
      rw [add_sub_right_comm, ← he]
      exact (norm_add_le _ _).trans (add_le_add hP1 h2)
    · have hy := MajInv.lact_mem_dom X (hG.isUStab s.2.1) hx0
      have h2 := (norm_tsum_le_tsum_norm (hs _ hy)).trans (tsum_le_of_le (hs _ hy)
        (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          rw [hn, ← FundSetPf.lact_mul]
          refine hP0 _ (G.mul_mem (hG.1 γ.2) s.2.1) fun h => s.2.2 ?_
          rw [eq_inv_of_mul_eq_one_right h]
          exact X.Γ.inv_mem γ.2) hCs (hsum _ hy))
      exact h2.trans (by linarith)
  refine ⟨u, hu, by rw [hu1]; exact one_ne_zero, fun γ hγ hγ' => ?_⟩
  obtain ⟨s, hsT, hs⟩ := hT γ⁻¹ (hG.isUStab (G.inv_mem hγ))
  have e : s⁻¹ = (s⁻¹ * γ⁻¹) * γ := by group
  have e' : γ = (s⁻¹ * γ⁻¹)⁻¹ * s⁻¹ := by group
  have h1 : s⁻¹ ∈ G := by rw [e]; exact G.mul_mem (hG.1 hs) hγ
  have h2 : s⁻¹ ∉ X.Γ := fun h => hγ' (by rw [e']; exact X.Γ.mul_mem (X.Γ.inv_mem hs) h)
  have h3 : u (lact s⁻¹ x0) = 0 := hu0 ⟨⟨s, hsT⟩, h1, h2⟩
  have hu' : u ∈ X.SS la := hu
  rw [e', FundSetPf.lact_mul, hu'.1.1.2.2 _ (X.Γ.inv_mem hs) _
    (MajInv.lact_mem_dom X (hG.isUStab h1) hx0), h3, mul_zero]

open GlobalTheory.Up.BallExPf in

theorem frame_bound3 {r : ℕ} (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0)
    (h1 : IsOrth X x1) (hρ : rhX X x0 x1 ≤ 1 / 4) (τ : X.Ψ) (u : Fin r → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ)⁻¹ *ᵥ u) ≤ 3 * ReciprocityTheory.MultiplicativeHeights.normSq u ∧
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ) *ᵥ u) ≤ 3 * ReciprocityTheory.MultiplicativeHeights.normSq u := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have e : (3 : ℝ) = (1 + 1 / 2) / (1 - 1 / 2) := by norm_num
  rw [e]
  refine norm_bound X.p0_le _ ?_ (by norm_num) (by norm_num) ?_ u
  · have a0 := (gram_iff X τ.1 _).1 (h0 τ)
    have a1 := (gram_iff X τ.1 _).1 (h1 τ)
    conv_lhs => rw [← a0]
    rw [← a1]
    conv_rhs => rw [← Matrix.mul_nonsing_inv_cancel_left _ (mat x1 τ) hu, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · have := neg_log_factor_le_rhX h0 (IW.orth_mem_dom X x1 h1) τ
    rw [FramePotential.norm_dmin_of_isOrth X h1] at this
    exact this.trans (hρ.trans (by norm_num))

theorem norm_lminor_le {r : ℕ} (g : Matrix (Fin r) (Fin r) ℂ)
    (hg : ∀ u, ReciprocityTheory.MultiplicativeHeights.normSq (g *ᵥ u) ≤ 3 * ReciprocityTheory.MultiplicativeHeights.normSq u) (i : Fin (r + 1)) :
    ‖lminor g i‖ ≤ (r.factorial : ℝ) * 2 ^ r := by
  have he : ∀ a b, ‖g a b‖ ≤ 2 := fun a b => by
    have h := hg (Pi.single b 1)
    have h1 : ReciprocityTheory.MultiplicativeHeights.normSq (Pi.single b 1 : Fin r → ℂ) = 1 := by
      unfold ReciprocityTheory.MultiplicativeHeights.normSq
      rw [Finset.sum_eq_single b] <;> simp +contextual [Pi.single_apply]
    have h2 : ‖g a b‖ ^ 2 ≤ ReciprocityTheory.MultiplicativeHeights.normSq (g *ᵥ Pi.single b 1) := by
      unfold ReciprocityTheory.MultiplicativeHeights.normSq
      have := Finset.single_le_sum (f := fun k => ‖(g *ᵥ Pi.single b 1) k‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ a)
      simpa using this
    rw [h1] at h
    nlinarith [norm_nonneg (g a b)]
  have hi := Nat.le_of_lt_succ i.isLt
  have h := Matrix.det_le (A := g.submatrix (Fin.castLE hi) (Fin.castLE hi)) (abv := NormedField.toAbsoluteValue ℂ)
    (x := 2) fun a b => he _ _
  rw [Fintype.card_fin, nsmul_eq_mul] at h
  refine le_trans h ?_
  gcongr
  norm_num

theorem neg_Lm_le {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (hρ : rhF X x0 z ≤ 1 / 4) (τ : X.Ψ) (i : Fin (r + 1)) :
    -IW.Lm X (cpt X x0 z) τ i ≤ 2 * Real.log ((r.factorial : ℝ) * 2 ^ r) := by
  have hz' : cpt X x0 z ∈ X.dom := hz
  obtain ⟨x1, h1, b, hb, e⟩ := ortho_holds r X _ hz'
  have hf := FramePotential.factor_rmul X x0 x1 hb τ i
  rw [← e, FramePotential.lminor_cpt X h0, FramePotential.norm_dmin_of_isOrth X h1, norm_one, one_pow, div_one] at hf
  have hr : rhX X x0 x1 ≤ 1 / 4 := by rw [← rhX_rmul x0 x1 hb, ← e, rhX_cpt h0 hz]; exact hρ
  have hl := norm_lminor_le _ (fun u => (frame_bound3 X h0 h1 hr τ u).2) i
  have hpos : 0 < ‖dmin X.Gm (cpt X x0 z) τ i‖ := norm_pos_iff.2 (IW.dmin_ne_zero X hz' τ i)
  have hl0 : 0 < ‖lminor ((mat x0 τ)⁻¹ * mat x1 τ) i‖ := by
    refine norm_pos_iff.2 fun h => ?_
    rw [hf, h] at hpos
    simp at hpos
  unfold IW.Lm
  rw [hf, one_div, Real.log_inv, neg_neg, Real.log_pow]
  push_cast
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hl0 hl) (by norm_num)

theorem sum_by_parts (a L : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a i * (L (i + 1) - L i) =
      a n * L n - a 0 * L 0 + ∑ i ∈ Finset.range n, (a i - a (i + 1)) * L (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

theorem exists_phla_bound' {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) {la : Wt X.Ψ r}
    (hla : ∀ τ, ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) :
    ∃ A : ℝ, ∀ z ∈ OmF X x0, rhF X x0 z ≤ 1 / 4 → -phla X la (cpt X x0 z) ≤ A := by
  set C : ℝ := 2 * Real.log ((r.factorial : ℝ) * 2 ^ r) + 1 / 4 with hC
  have hC0 : 0 ≤ 2 * Real.log ((r.factorial : ℝ) * 2 ^ r) := by
    have h1 : (1 : ℝ) ≤ r.factorial := by exact_mod_cast r.factorial_pos
    have h2 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have := Real.log_nonneg (one_le_mul_of_one_le_of_one_le h1 h2)
    linarith
  let a : X.Ψ → ℕ → ℝ := fun τ k => if h : k < r then (la τ ⟨k, h⟩ : ℝ) else 0
  refine ⟨∑ τ, ∑ i ∈ Finset.range r, |a τ i - a τ (i + 1)| * C, fun z hz hρ => ?_⟩
  rw [IW.phla_eq X hz, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  set x := cpt X x0 z with hx
  let L' : ℕ → ℝ := fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have h3 : ∀ i : Fin r, (la τ i : ℝ) = a τ i := fun i => by simp only [a, dif_pos i.isLt]
  have hL0 : L' 0 = 0 := by simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 h0 z τ
  simp_rw [h1, h2, h3]
  rw [Fin.sum_univ_eq_sum_range (fun i => a τ i * (L' (i + 1) - L' i)) r, sum_by_parts, hL0, hLr, mul_zero, mul_zero,
    sub_zero, zero_add, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hir := Finset.mem_range.1 hi
  have hCn : 0 ≤ C := by linarith
  by_cases hr : i + 1 = r
  · rw [hr, hLr, mul_zero, neg_zero]; positivity
  by_cases hp : i + 1 = X.p0
  · have h4 : |L' (i + 1)| ≤ C := by
      have := abs_Lm_le X h0 hz τ
      simp only [L', dif_pos (Nat.succ_lt_succ hir)]
      have e : (⟨i + 1, Nat.succ_lt_succ hir⟩ : Fin (r + 1)) = ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ := Fin.ext hp
      rw [e]
      linarith
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  · have hi1 : i + 1 < r := by omega
    have h5 : 0 ≤ a τ i - a τ (i + 1) := by
      have := hla τ ⟨i, hir⟩ ⟨i + 1, hi1⟩ rfl hp
      simp only [a, dif_pos hir, dif_pos hi1]
      have : ((la τ ⟨i + 1, hi1⟩ : ℤ) : ℝ) ≤ la τ ⟨i, hir⟩ := by exact_mod_cast this
      linarith
    have h6 : -L' (i + 1) ≤ C := by
      simp only [L', dif_pos (Nat.succ_lt_succ hir)]
      have := neg_Lm_le X h0 hz hρ τ ⟨i + 1, Nat.succ_lt_succ hir⟩
      linarith
    rw [abs_of_nonneg h5, ← mul_neg]
    exact mul_le_mul_of_nonneg_left h6 h5

theorem normSq_sub_le {r : ℕ} (v w : Fin r → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.normSq (v - w) ≤ 4 / 3 * ReciprocityTheory.MultiplicativeHeights.normSq v + 4 * ReciprocityTheory.MultiplicativeHeights.normSq w := by
  unfold ReciprocityTheory.MultiplicativeHeights.normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h : ‖(v - w) k‖ ≤ ‖v k‖ + ‖w k‖ := norm_sub_le _ _
  nlinarith [norm_nonneg ((v - w) k), norm_nonneg (v k), norm_nonneg (w k), sq_nonneg (‖v k‖ - 3 * ‖w k‖)]

open ReciprocityTheory.MultiplicativeHeights in
open scoped ComplexOrder in

theorem eq_one_of_cong {K : Type} [Field K] [NumberField K] {r M : ℕ} (hM : 5 ≤ M)
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (L : Submodule (𝓞 K) (Fin r → K)) (γ : Matrix (Fin r) (Fin r) K) (hNC : NoContraction H L)
    (hb : ∀ (σ : K →+* ℂ) (w : Fin r → ℂ), hq (H σ) (γ.map σ *ᵥ w) ≤ 3 ^ 2 * hq (H σ) w)
    (hL : ∀ x ∈ L, ∃ y ∈ L, γ *ᵥ x - x = (M : K) • y) : γ = 1 := by
  have hM0 : (M : K) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hN : (M : K)⁻¹ • (γ - 1) = 0 := by
    refine hNC _ (fun x hx => ?_) (fun σ u hu => ?_)
    · obtain ⟨y, hy, e⟩ := hL x hx
      rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, e, smul_smul, inv_mul_cancel₀ hM0, one_smul]
      exact hy
    · obtain ⟨Q, hQdet, hQ⟩ := sb_exists_root (hH σ)
      have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQdet
      have hQu0 : Q *ᵥ u ≠ 0 := by
        intro h0
        apply hu
        have := congrArg (fun v => Q⁻¹ *ᵥ v) h0
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQu] using this
      have hmap : ((M : K)⁻¹ • (γ - 1)).map σ = (M : ℂ)⁻¹ • (γ.map σ - 1) := by
        ext a b
        by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
      have h1 := hb σ u
      rw [hQ, hQ] at h1
      rw [hQ, hQ, hmap, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_sub]
      have h2 := normSq_sub_le (Q *ᵥ (γ.map σ *ᵥ u)) (Q *ᵥ u)
      have h3 := sb_normSq_pos hQu0
      generalize Q *ᵥ (γ.map σ *ᵥ u) - Q *ᵥ u = v at h2 ⊢
      have h4 : normSq ((M : ℂ)⁻¹ • v) = ((M : ℝ) ^ 2)⁻¹ * normSq v := by
        unfold normSq
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [mul_pow]
      have h5 : (25 : ℝ) ≤ (M : ℝ) ^ 2 := by
        have : (5 : ℝ) ≤ M := by exact_mod_cast hM
        nlinarith
      rw [h4, inv_mul_lt_iff₀ (by linarith)]
      nlinarith
  exact sub_eq_zero.1 ((smul_eq_zero.1 hN).resolve_left (inv_ne_zero hM0))

open GlobalTheory.Up.BallExPf in

theorem exists_freeBall {r : ℕ} (X : DataX E r) {N : ℕ} (hN : 5 ≤ N)
    (hL : ∀ γ ∈ X.Γ, ∀ x ∈ X.L', ∃ y ∈ X.L', (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (N : E) • y) :
    ∃ x0, IsOrth X.toData x0 ∧ FreeBall X.toData X.Γ x0 (1 / 4) := by
  have hU := X.Γ_stab
  obtain ⟨M, -, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact exists_frame (M.posDef τ.1) (M.major τ.1) hP ((gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have hx0 : ∀ τ, mat x0 τ = y τ := fun _ => rfl
  have h0 : IsOrth X.toData x0 := fun τ => (gram_iff X.toData τ.1 _).2 (hy1 τ)
  refine ⟨x0, h0, le_rfl, hU, fun γ hγ hne x hx hlt => ?_⟩
  by_contra hlt2
  rw [not_le] at hlt2
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  rw [FundSetPf.lact_rmul, rhX_rmul _ _ hb] at hlt2
  rw [rhX_rmul _ _ hb] at hlt
  have h2 := isOrth_lact_of_isUStab (hU γ hγ) h1
  have hk : (0 : ℝ) ≤ 3 := by norm_num
  have hΨ : ∀ (τ : X.Ψ) (w : Fin r → ℂ),
      ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) ((γ : Matrix (Fin r) (Fin r) E).map τ.1 *ᵥ w) ≤
        3 ^ 2 * ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
    intro τ w
    have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X.toData x0 h0 τ)
    have hu1 : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)
    have hH : M.H τ.1 = ((y τ)⁻¹)ᴴ * (y τ)⁻¹ := by
      calc M.H τ.1 = (y τ * (y τ)⁻¹)ᴴ * M.H τ.1 * (y τ * (y τ)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hu]; simp
        _ = ((y τ)⁻¹)ᴴ * ((y τ)ᴴ * M.H τ.1 * y τ) * (y τ)⁻¹ := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hy2, Matrix.mul_one]
    rw [hH, hq_ct_mul, hq_ct_mul]
    have b1 := (frame_bound3 X.toData h0 h1 hlt.le τ ((y τ)⁻¹ *ᵥ w)).1
    have b2 := (frame_bound3 X.toData h0 h2 hlt2.le τ ((mat x1 τ)⁻¹ *ᵥ w)).2
    have e : mat (lact γ x1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ := rfl
    rw [hx0, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu] at b1
    rw [hx0, e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1,
      ← Matrix.mulVec_mulVec] at b2
    calc _ ≤ _ := b2
      _ ≤ _ := mul_le_mul_of_nonneg_left b1 hk
      _ = _ := by ring
  refine hne (Units.ext (eq_one_of_cong hN M.H M.posDef X.L' _ hNC (fun σ w => ?_) (hL γ hγ)))
  · by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩ w
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := not_not.1 fun h' => hσ ((X.cmType σ).2 h')
      have h := hΨ ⟨_, hσ'⟩ (star w)
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : (γ : Matrix (Fin r) (Fin r) E).map (ComplexEmbedding.conjugate σ) *ᵥ star w =
          star ((γ : Matrix (Fin r) (Fin r) E).map σ *ᵥ w) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, hq_conj, hq_conj] at h

theorem exists_cusp_centre {r : ℕ} (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0)
    (hFB : FreeBall X X.Γ x0 (1 / 4)) (la : Wt X.Ψ r)
    (hla : ∀ τ, ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i)
    (hp : ∀ τ, ∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 →
      ((4 * X.Ψ.card * r ^ 2 + 4 * dimX X + 2 * r : ℕ) : ℤ) ≤ la τ i1 - la τ i0) :
    ∃ P ∈ X.SS la, P x0 ≠ 0 := by
  have hd : 1 ≤ dimX X := (one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · unfold dimX at hd; rw [h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 la (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 4 * dimX X + 2)).2
    (fun τ => ⟨fun i j hj hp' => by
      have := hla τ i j hj hp'
      have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
      simp only [Pi.sub_apply, kapW, hj']
      omega, fun i0 i1 h0' h1' => by
      have := hp τ i0 i1 h0' h1'
      have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
      simp only [Pi.sub_apply, kapW, h0', h1', hr]
      have h2 : (((4 * X.Ψ.card * r ^ 2 + 4 * dimX X + 2 * r : ℕ) : ℤ) : ℝ) ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ) := by
        exact_mod_cast this
      push_cast at h2 ⊢
      linarith⟩) x0 hx0
  obtain ⟨P, hP, hne, -⟩ := orbitInterp' r X X.Γ x0 la (1 / 4) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) _ hx0 hd
    (by norm_num) hFB (exists_phla_bound' X hx0 hla) (by linarith) (by
      have : (dimX X : ℝ) / (1 / 4) = 4 * dimX X := by ring
      linarith) hcurv
    (cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (hla _) fun i0 i1 h0' h1' => by
      have := hp ⟨τ, hτ⟩ i0 i1 h0' h1'
      omega)
  exact ⟨P, hP, hne⟩

end GlobalTheory.CentreCusp
