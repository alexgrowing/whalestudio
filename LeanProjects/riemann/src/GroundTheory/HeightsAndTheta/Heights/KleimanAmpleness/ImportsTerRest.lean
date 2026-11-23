import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveComap.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ e : ℕ,
        (relDim W = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
          Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
