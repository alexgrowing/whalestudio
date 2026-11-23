import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBound
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.HermitianCurvature.StatementTBB
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_bessel_scale_bound : ∃ c₃ : ℝ, ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (A b C₄ Cb : ℝ) (n₀ p₀ : ℕ), IsStdOf L μsec p.T.base → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → c₃ * ((D.R.rS : ℝ) + 1) ^ 2 * ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 f → 3 ≤ b → C₄ + 1 ≤ Cb → ((2 * p₀ + n₀ : ℕ) : ℝ) ≤ Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 → TBB.ThmBpAt p f b C₄ n₀ p₀ → ∀ γ : Point ℂ (D.R.rS + 1), ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → ThB.BpIneq D Cb L f μsec b γ := by
  first | exact @GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt | exact GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt | (intros; apply GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt <;> assumption)
