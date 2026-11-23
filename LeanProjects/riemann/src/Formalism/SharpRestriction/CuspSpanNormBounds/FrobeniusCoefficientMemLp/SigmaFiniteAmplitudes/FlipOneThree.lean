import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem amplitude_orbital_integral : Formalism.MainNotions.S.Pv.AmpDD.AmpDDOfSteps := by
  intro hSchH hNI hGG _hDD hRS hIn k r L h μG w0 l l' hOP γ μR νR ν hCD b hb hab' hpm v hv v' hv' ξ ξ'
  obtain ⟨hgap, hOK, -, hw0, hμG, hl, hl'⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay L.σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hw0DD : w0 ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0 := by
    have := Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 (Formalism.FourierDecayAlt.P.S3dx6.one_mem_uh (k := k) (r := r))
    rwa [(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ).1, ContinuousLinearMap.one_apply] at this
  obtain ⟨C1, hC1⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v' hv'
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by linarith
  have hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - Formalism.FourierDecayAlt.ThreeDimData.aOf r h)) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core L hμG hd hSch hNI hw1 l l' hl hl' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm hv hv' hC1 hC2 ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
