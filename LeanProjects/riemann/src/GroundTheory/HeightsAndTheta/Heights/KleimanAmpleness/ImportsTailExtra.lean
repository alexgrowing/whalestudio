import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (n : ℕ) (μs : Fin n → K → ℤ),
      NumbersDVR.intNum F (mIdealOver F (segreJoin y)) (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
