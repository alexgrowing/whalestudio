import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.DiagB

def AmpUnifP : Prop :=
  ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Formalism.BasicNotions.Ties D → Formalism.MainNotions.S.Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 0 C1 Ca

end GlobalTheory.DiagB
