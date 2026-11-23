import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalSquare_eq_hilbertSchmidt_normalisedVector : ∃ c₃ : ℝ, ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN A : ℝ) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.IsBaseFrame Bs ν' m₀ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 F → ∀ γ : Point ℂ (r + 1), 0 < ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ → ThB.orbSq L F γ = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 * ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2) := by
  first | exact @GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | exact GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | (intros; apply GlobalTheory.ThA.OrbSq.orbSq_eq_vecV <;> assumption)
