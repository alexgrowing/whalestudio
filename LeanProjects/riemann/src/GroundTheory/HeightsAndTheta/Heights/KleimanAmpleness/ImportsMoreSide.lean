import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefFibresSegreSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelGenericPoint.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (NumbersDVR.MRing ι O)) (d : ℕ),
    NumbersDVR.IsModelOver P d →
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra O Ω) (_ : Algebra (FractionRing O) Ω)
      (_ : IsScalarTower O (FractionRing O) Ω) (y : (Σ k, ι k) → Ω),
      mIdealOver O y = P ∧ ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0

example (h : ModelGenericPoint.Statement) :=
  h exO Unit (fun _ => Fin 2) ⊥ 1 NefFibresSegre.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
