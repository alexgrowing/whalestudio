import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.MeasurableMulInvInv

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section OneSide

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem op_eq_sum (T : Wp →L[ℂ] Wp) :
    T = ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (T ((stdOrthonormalBasis ℂ Wp) i)) := by
  ext x
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wp).sum_repr' x]
  rw [map_sum]
  simp only [map_smul]

def piOp (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (h : Mt k r) : Wp →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight (piV z π ((stdOrthonormalBasis ℂ Wp) i) h)

theorem sm_piOp {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) : StronglyMeasurable (piOp (k := k) (r := r) z π) := by
  have hs := Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin (Module.finrank ℂ Wp)))
    (f := fun i (h : Mt k r) => (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i)).smulRight
      (piV z π ((stdOrthonormalBasis ℂ Wp) i) h))
    (fun i _ => (ContinuousLinearMap.smulRightL ℂ Wp Wp
      (innerSL ℂ ((stdOrthonormalBasis ℂ Wp) i))).continuous.comp_stronglyMeasurable (sm_piV hT hπ _))
  convert hs using 1
  funext h
  unfold piOp
  rw [Finset.sum_apply]

theorem piOp_eq (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) {h : Mt k r}
    (hh : Matrix.of h ∈ UWset k r z) : piOp z π h = π (Matrix.of h) := by
  rw [op_eq_sum (π (Matrix.of h))]
  unfold piOp
  congr 1
  funext i
  rw [show piV z π ((stdOrthonormalBasis ℂ Wp) i) h = π (Matrix.of h) ((stdOrthonormalBasis ℂ Wp) i) from
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hh _]

end OneSide

section Be

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem aVec_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p1 : Mt k r × Mt k r) :
    aVec z c π σ w0 v ξ t p1 = Formalism.FourierDecayAlt.P.S3dx6.aInt z c π σ w0 v t p1 ξ := rfl

theorem norm_pi_le_one {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : ‖π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h hh, one_mul]

theorem aesm_beInt {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  let F : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
    (cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) * star (psi k r z c (Matrix.of p.2))) •
      piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1)
  have hF : StronglyMeasurable F := by
    have hc : Measurable fun p : Mt k r × Mt k r =>
        cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) :=
      (meas_cM hσ v w0).comp (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM measurable_fst measurable_snd)
        measurable_const)
    have hps : Measurable fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2)) :=
      (continuous_star.comp (Formalism.FourierDecayAlt.P.S3dx6.continuous_psi z c)).measurable.comp measurable_snd
    exact (hc.mul hps).stronglyMeasurable.smul
      ((sm_piOp hT hπ).comp_measurable (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp measurable_fst))
  refine hF.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hp1.1 hp2.1
  have hm : Matrix.of p.1 * Matrix.of p.2 * t ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhn ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ t w0)⟫_ℂ := by
    rw [show cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM p.1 p.2) (t : Mt k r)) =
      ⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * t) w0⟫_ℂ from
      Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) hm _]
    rw [hU.2.1 _ hhn _ ht]
    rfl
  have e2 : piOp z π (Formalism.FourierDecayAlt.P.B7.invM p.1) = π (Matrix.of p.1)⁻¹ :=
    piOp_eq z π (h := Formalism.FourierDecayAlt.P.B7.invM p.1) (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp1).1
  show F p = _
  simp only [F, e1, e2]
  rfl

variable [CompleteSpace Wp]

theorem int_beInt_of {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    (hξ : ξ ≠ 0) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (ha : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN)) :
    Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have hae := aesm_beInt hσ hT hπ c w0 v ht h1 h2
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hcomp : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v ∘ Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) := by
    refine (ha.norm.div_const ‖ξ‖).mono' (hae.comp_measurePreserving hι) ?_
    filter_upwards [h1', h2'] with p hp1 hp2
    rw [Function.comp_apply, Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    unfold Formalism.FourierDecayAlt.P.S3dx6.aInt
    rw [norm_smul, _root_.smul_apply, norm_smul,
      Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ _ hp1, le_div_iff₀ hξn]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (norm_pi_le_one hT hπ hp1))
      (norm_nonneg ξ)
  exact (hι.integrable_comp hae).mp hcomp

theorem int_a_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μW μW)
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μN μN)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    (l : H → Wp)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = (innerSL ℂ (l v)).smulRight (l (σ t w0)))
    (hA : Integrable (aVec z c π σ w0 v ξ t) (μW.prod μN) ∨ ∀ᵐ p ∂(μW.prod μN), aVec z c π σ w0 v ξ t p = 0) :
    ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  have hι : MeasurePreserving (Prod.map (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) Formalism.FourierDecayAlt.P.B7.invM)
      (μW.prod μN) (μW.prod μN) := hιW.prod hιN
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  have hval : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ = ⟪l v, ξ⟫_ℂ • l (σ t w0) := by
    rw [hbe, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  by_cases hI : Integrable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v) (μW.prod μN)
  · have e1 : (Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v) ξ =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) :=
      ContinuousLinearMap.integral_apply hI ξ
    have hg : AEStronglyMeasurable (fun p => Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ)
        (Measure.map (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM) (μW.prod μN)) := by
      rw [hι.map_eq]; exact hI.aestronglyMeasurable.apply_continuousLinearMap ξ
    have e2 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v p ξ ∂(μW.prod μN) =
        ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) := by
      rw [← integral_map hι.measurable.aemeasurable hg, hι.map_eq]
    have e3 : ∫ p, Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ (σ t w0) v (Prod.map Formalism.FourierDecayAlt.P.B7.invM Formalism.FourierDecayAlt.P.B7.invM p) ξ
          ∂(μW.prod μN) = ∫ p, aVec z c π σ w0 v ξ t p ∂(μW.prod μN) := by
      refine integral_congr_ae ?_
      filter_upwards [h1', h2'] with p hp1 hp2
      rw [Formalism.FourierDecayAlt.P.S3dx6.aInt_eq hz c π hU w0 v ht hp1 hp2, aVec_eq]
    rw [← e3, ← e2, ← e1, hval]
  · have hbe0 : Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ t w0) v = 0 := integral_undef hI
    rw [hbe0, _root_.zero_apply] at hval
    rw [← hval]
    rcases hA with hA | hA
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [aVec]
      · exact absurd (int_beInt_of hσ hz hT hπ c w0 v ξ hξ ht hιW hιN h1 h2 hA) hI
    · exact integral_eq_zero_of_ae hA

end Be

end Formalism.MainNotions.S.Pv.AmpDDPf
