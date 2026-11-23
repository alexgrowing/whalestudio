import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSection
import Formalism.HermitianCurvature.StatementTBB
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_frame_section' : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r), D.IsBaseFrame Bs ν' m₀ → ∃ γ : (Fin (r + 1) → ℂ) → B.Mat k r, ContinuousOn γ {c | (∀ a, c a ≠ 0) ∧ Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r))} ∧ ∀ c : Fin (r + 1) → ℂ, (∀ a, c a ≠ 0) → Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r)) → γ c ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (γ c) = D.ptMatN (TBB.bigPt r c) (r + 1) ∧ D.IsDFrame Bs ν' m₀ (γ c) := by
  first | exact @GlobalTheory.FrameSection.exists_continuous_frame_section | exact GlobalTheory.FrameSection.exists_continuous_frame_section | (intros; apply GlobalTheory.FrameSection.exists_continuous_frame_section <;> assumption)
