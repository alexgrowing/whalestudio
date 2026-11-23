import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.GapDegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem deg_eq_mul_fdegH : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW
  have hμ : PI.BesselPeriodGGP.IsHaarOn (GG D.R.k D.R.rS) W.μG := hW.2.2.2.2.2.2.1
  by_cases hQ : ∃ Q, IsCayley D.R.k D.R.rS (epsSH D.R) Q
  swap
  · refine ⟨1, one_pos, fun lam A hA _ => absurd ?_ hQ⟩
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hQd hQ.2 W.μG hμ
  set s : ℝ≥0∞ := ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) with hs
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2 (D.s.cdScale_pos _ _).ne'
  have hst : s ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : a / s ≠ 0 := (ENNReal.div_pos ha0 hst).ne'
  have hbt : a / s ≠ ∞ := (ENNReal.div_lt_top hat hs0).ne
  have hκ : 0 < (a / s).toReal := ENNReal.toReal_pos hb0 hbt
  refine ⟨(a / s).toReal, hκ, fun lam A hA _ v hv => ?_⟩
  obtain ⟨P, hP, hd, hS⟩ := hA.2.2.2.2.2.2.2.2.2.2
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hme : MeasurableEmbedding (phi (epsSH D.R) P) :=
    (phi_closedEmbedding (ε := epsSH D.R) Formalism.REAL.isClosedEmbeddingMatrix hPd).measurableEmbedding
  have hb : W.μG = (a / s) • (s • Formalism.REAL.muG (epsSH D.R)).map (phi (epsSH D.R) P) := by
    rw [Measure.map_smul, smul_smul, ENNReal.div_mul_cancel hs0 hst, GlobalTheory.DegreeTie.map_phi_eq hP hQ]
    exact ha
  have hf : PI.BesselPeriodGGP.fdegH W.μG A.σ v = A.deg / (a / s).toReal := by
    refine Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq (div_pos hd hκ) (fun v w v' w' => ?_) hv
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [hb]
    constructor
    · refine Integrable.smul_measure ?_ hbt
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, A.σ (Matrix.of (phi (epsSH D.R) P g)) v⟫_ℂ *
          star ⟪w', A.σ (Matrix.of (phi (epsSH D.R) P g)) v'⟫_ℂ
          ∂(s • Formalism.REAL.muG (epsSH D.R)) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((A.deg : ℝ) : ℂ) := h2
      rw [h3, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  refine ⟨?_, hd⟩
  rw [hf]
  field_simp

end GlobalTheory.GapDegreeTie

end
