import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapSetup

theorem isFamG_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) :
    IsFamG lam q0 R := by
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  intro ν hν
  have hd := hF ν hν
  exact ⟨hd.1, hd.2, ⟨h / 2, (H.2 ν hν).2.2.1, H.1.2.2.2.2⟩⟩

theorem families_gap : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  refine ⟨isFamG_of_num, ?_⟩
  intro k r Wp _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg
  constructor
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, isFamG_of_num k r lam u b bv ga h q0 R hN hF, hS, hSF⟩
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, fun ν hν => GlobalTheory.isDS_of_isDG (hF ν hν), hS, hSF⟩

end GlobalTheory.GapSetup
