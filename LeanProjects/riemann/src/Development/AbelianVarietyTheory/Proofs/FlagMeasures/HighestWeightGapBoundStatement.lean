import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_gap_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g₀ : ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) → 2 * (n : ℝ) < g₀ → ∀ F : Matrix (Fin n) (Fin n) ℂ → (H →ₗ[ℂ] H), (∀ g ∈ UJset ε, ∀ x ∈ (kSpan ε E u).map V.subtype, F g x ∈ (kSpan ε E u).map V.subtype ∧ ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, F (k₁ * g * k₂) x = σ k₁ (F g (σ k₂ x))) → (∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, SmoothOnG ε (fun g => ⟪y, F g x⟫_ℂ)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ⟪y, F z (at1 G a b : V)⟫_ℂ) (umat g) = 0) → (∀ x ∈ (kSpan ε E u).map V.subtype, F 1 x = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, Eword ε w (fun g => ⟪y, F g x⟫_ℂ) 1 = 0 := by
  first | exact @GlobalTheory.Jet.Germ.germ_jet_zero | exact GlobalTheory.Jet.Germ.germ_jet_zero | (intros; apply GlobalTheory.Jet.Germ.germ_jet_zero <;> assumption)
