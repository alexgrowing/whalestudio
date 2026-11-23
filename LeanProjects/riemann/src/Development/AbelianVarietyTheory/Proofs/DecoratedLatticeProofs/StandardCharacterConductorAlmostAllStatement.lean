import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_conductor_almost_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.Conductor.eventually_conductor | exact GlobalTheory.FinPl.Conductor.eventually_conductor | (intros; apply GlobalTheory.FinPl.Conductor.eventually_conductor <;> assumption)
