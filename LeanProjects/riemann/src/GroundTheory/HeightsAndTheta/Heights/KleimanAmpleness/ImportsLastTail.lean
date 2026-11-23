import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def PointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω),
    relDim (mIdealOver F y) = ((0 : ℕ) : WithBot (WithTop ℤ)) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)

example (F : Type) [Field F] (h : PointChartField.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 0) (fun _ => 0) (fun _ => IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero F 0 _)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
