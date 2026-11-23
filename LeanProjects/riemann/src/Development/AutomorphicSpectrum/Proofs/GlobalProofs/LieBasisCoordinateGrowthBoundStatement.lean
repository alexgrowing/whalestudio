import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_basis_coordinate_growth_bound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i)) (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w → dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w) {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C) (hbound : ∀ l : List (Fin d), ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial), WordBound G π v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis <;> assumption)
