import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.AeInPairPair

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem measurable_pairMaj (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) :
    Measurable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj (k := k) (r := r) γ b) := by
  let g0 : Mt k r := γ
  have hM : Measurable fun p : PairSp k r =>
      Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM
        (Formalism.FourierDecayAlt.P.B7.invM p.1.1) (Formalism.FourierDecayAlt.P.B7.invM p.1.2)) g0) p.2.2) p.2.1 :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM
      (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp (measurable_fst.comp measurable_fst))
      (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp (measurable_snd.comp measurable_fst))) measurable_const)
      (measurable_snd.comp measurable_snd)) (measurable_fst.comp measurable_snd)
  exact (meas_gN_rpow (-b)).comp hM

theorem sigmaFinite_nu (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν) (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {b : ℝ}
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν) : SigmaFinite ν := by
  refine sigmaFinite_of_weight ν (fun p => ENNReal.ofReal (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p))
    (ENNReal.measurable_ofReal.comp (measurable_pairMaj γ b)) ?_ ?_
  · have h := hpm.2
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) h
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · have hae : ∀ᵐ p ∂ν, ¬ (ENNReal.ofReal (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) = 0) := ?_
    · have := ae_iff.mp hae
      simpa only [not_not] using this
    filter_upwards [ae_inPair_nu L hμR hOQ] with p hp
    obtain ⟨hh, hn, hh', hn'⟩ := hp
    have hM : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 ∈ UH (Hpk k r) :=
      PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh.1).2.2
        (PI.WBL.Cv.uh_inv hn.1).2.2) hγ) hn'.1) hh'.1
    have h1 := ((hNI k r).2 _ hM).2
    have hpos : 0 < Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p := by
      unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
      exact Real.rpow_pos_of_pos (by linarith) _
    simpa using hpos

end Formalism.MainNotions.S.Pv.AmpDDPf
