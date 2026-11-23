import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeBadFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : K → ℤ),
    {a : (Σ k, ι k) → ℤ | blockSum a = e ∧ ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ}.Finite

end

end GroundTheory.Heights₂.Heights.Kleiman
