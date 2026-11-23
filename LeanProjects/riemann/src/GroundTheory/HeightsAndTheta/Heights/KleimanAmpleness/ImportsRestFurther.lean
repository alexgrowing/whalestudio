import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def RatioDim.Statement : Prop :=
  ∀ (k : Type) [Field k] (N m : ℕ) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)), W.IsPrime →
    NumbersDVR.IsMultiHomogIdeal W → ∀ j : Fin m,
      (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
      (∀ b : Fin m, ∃ f g : Kleiman.Poly k N,
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W) →
      ringKrullDim (NumbersDVR.MRing (graphIdx N m) k ⧸ W) =
        ringKrullDim (Kleiman.Poly k N ⧸ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) + 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
