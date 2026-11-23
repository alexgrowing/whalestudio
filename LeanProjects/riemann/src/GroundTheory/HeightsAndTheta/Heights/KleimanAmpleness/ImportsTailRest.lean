import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ a, Fintype (ι a)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ a, ι a) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ a, ∃ i, y ⟨a, i⟩ ≠ 0) → FieldNumbers.relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∃ (N : ℕ) (eqv : (∀ a, ι a) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω)
      (Ms : Fin d → Kleiman.LineBundle F x),
      (∀ i, x (eqv i) = ∏ a, y ⟨a, i a⟩) ∧
      Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d ∧
      (∀ j (c : ℤ), ((Ms j).twist (Kleiman.twistSys F x c)).secs =
        secOver F y (μs j + fun _ => c)) ∧
      (∀ j, Kleiman.Nef (Ms j).toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (μs j)) ∧
      Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun j => (Ms j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
