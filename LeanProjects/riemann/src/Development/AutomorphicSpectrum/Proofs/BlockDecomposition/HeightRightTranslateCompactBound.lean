import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtRightTranslate

theorem height_mul_le : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H →
    (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  rintro D n H hH ⟨C₀, hC₀, hcov⟩ C hC
  have hcont : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
  have hpos : ∀ g, 0 < (H g : ℝ) := fun g => by exact_mod_cast hH.2.1 g
  have hF : Continuous fun p : G D n × G D n => (H (p.1 * p.2) : ℝ) / (H p.1 : ℝ) :=
    (hcont.comp (continuous_fst.mul continuous_snd)).div (hcont.comp continuous_fst)
      fun p => (hpos p.1).ne'
  obtain ⟨M, hM⟩ := (hC₀.prod hC).bddAbove_image hF.continuousOn
  refine ⟨max M 1, le_max_right _ _, fun c hc x => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := hcov x
  have hb : (H (k * c) : ℝ) / (H k : ℝ) ≤ max M 1 :=
    (hM ⟨(k, c), ⟨hk, hc⟩, rfl⟩).trans (le_max_left _ _)
  have hb' : (H (k * c) : ℝ) ≤ max M 1 * (H k : ℝ) := (div_le_iff₀ (hpos k)).1 hb
  have hl := hH.2.2 q hq (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  rw [mul_assoc, hl (k * c), hl k]
  push_cast
  have hd : (0 : ℝ) ≤ (absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩)) : ℝ) :=
    NNReal.coe_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hb' hd]

end GlobalTheory.CompanionTheory.HtRightTranslate
