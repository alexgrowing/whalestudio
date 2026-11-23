import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMajInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem growth_side {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤) {β : ℝ} (hβ : Formalism.FourierDecayAlt.ThreeDimData.AG k r < β) :
    ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β))
      ∂(μW.prod (haarLie (Nset k r) κ)) < ⊤ := by
  set μN := haarLie (Nset k r) κ with hμN
  obtain ⟨μG, hμG⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  have hGsk : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG :=
    ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩
  have hS := Formalism.L2.SG.Pf.Choice.isHaarOn_muS hz hT hW hW1 hκ0 hκt
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists k r z hz hT μG _ hGsk hS
  have hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeCSB.haarLieN k r κ hκ0 hκt
  have hgr := Formalism.FourierDecayAlt.P.growth_spherical_bound k r z μW μN μG νq β hz hT hW hN hGsk hq hβ
  have hβ0 : 0 < β := lt_of_le_of_lt (by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity) hβ
  have hI : ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p =>
      Real.rpow_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _) _)).1 hgr.2

  obtain ⟨CW0, hCW0⟩ := (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT).exists_bound_of_continuousOn
    (f := fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Formalism.FourierDecayAlt.B.gN x)
    Formalism.FourierDecayAlt.P.s3dx1S_gNc.continuousOn
  set CW := max CW0 1 with hCW
  have hCW1 : 1 ≤ CW := le_max_right _ _
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound k r
  have : SigmaFinite μW := hW.1
  have : SFinite μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have hpt : ∀ᵐ p ∂(μW.prod μN), ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ≤
      ENNReal.ofReal ((CW * CW) ^ β) * ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) := by
    refine hae.mono fun p hp => ?_
    set h := Matrix.of p.1
    set n := Matrix.of p.2
    have hhU : h ∈ UH (Hpk k r) := hp.1.1
    have hhu : IsUnit h.det := uh_isUnit hhU
    have hnh : n * h ∈ UH (Hpk k r) := PI.WUN.UH_mul hp.2.1 hhU
    have hhn : h * n ∈ UH (Hpk k r) := PI.WUN.UH_mul hhU hp.2.1
    have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN (h * n) := (hNI.2 _ hhn).2
    have hgh : Formalism.FourierDecayAlt.B.gN h ≤ CW := by
      have := hCW0 h hp.1
      rw [Real.norm_of_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _)] at this
      exact this.trans (le_max_left _ _)
    have hghi : Formalism.FourierDecayAlt.B.gN h⁻¹ ≤ CW := by rw [(hNI.2 h hhU).1]; exact hgh
    have hle : Formalism.FourierDecayAlt.B.gN (h * n) ≤ CW * CW * Formalism.FourierDecayAlt.B.gN (n * h) := by
      have e : h * n = h * (n * h) * h⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.mul_one]
      rw [e]
      calc Formalism.FourierDecayAlt.B.gN (h * (n * h) * h⁻¹) ≤ Formalism.FourierDecayAlt.B.gN (h * (n * h)) * Formalism.FourierDecayAlt.B.gN h⁻¹ := hNI.1 _ _
        _ ≤ (Formalism.FourierDecayAlt.B.gN h * Formalism.FourierDecayAlt.B.gN (n * h)) * CW :=
            mul_le_mul (hNI.1 _ _) hghi (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _)
              (mul_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _) (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _))
        _ ≤ (CW * Formalism.FourierDecayAlt.B.gN (n * h)) * CW :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgh (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _))
              (by linarith)
        _ = CW * CW * Formalism.FourierDecayAlt.B.gN (n * h) := by ring
    have hpos : 0 < Formalism.FourierDecayAlt.B.gN (h * n) / (CW * CW) := div_pos (by linarith) (by positivity)
    have hle' : Formalism.FourierDecayAlt.B.gN (h * n) / (CW * CW) ≤ Formalism.FourierDecayAlt.B.gN (n * h) := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hm := Real.rpow_le_rpow_of_nonpos hpos hle' (by linarith : -β ≤ 0)
    rw [Real.div_rpow (by linarith) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ CW * CW),
      div_inv_eq_mul] at hm
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    exact ENNReal.ofReal_le_ofReal (hm.trans_eq (mul_comm _ _))
  calc ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal ((CW * CW) ^ β) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((CW * CW) ^ β) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-β)) ∂(μW.prod μN) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
