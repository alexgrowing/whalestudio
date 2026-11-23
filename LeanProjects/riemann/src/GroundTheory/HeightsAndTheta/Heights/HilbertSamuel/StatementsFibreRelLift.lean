import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreRelLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (ℓ : ℕ) (a : K → ℤ) (r : ℕ) (s : Fin r → Ω)
    (J : KH.Cell K ι 0)
    (u : Fin r → LocalizedModule (KH.cellMon (ZMod ℓ) J.1) (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))),
    (∀ j, s j ∈ chartLat y a 1) → (∀ k, y ⟨k, GenOnFibres.cellChart J k⟩ ≠ 0) →
    (∀ j, u j ∈ KH.locPart ι (KH.quotPart (ZMod ℓ) (GenOnFibres.idealOver y (ZMod ℓ))) (KH.cellMon (ZMod ℓ) J.1) (-a)) →
    ∑ j, u j * GenOnFibres.secCoch y (ZMod ℓ) (s j) a J = 1 →
    ∃ (u' : Fin r → Ω) (v : Ω), (∀ j, u' j ∈ chartRingZ y (GenOnFibres.cellChart J)) ∧
      v ∈ chartRingZ y (GenOnFibres.cellChart J) ∧
      ∑ j, u' j * (s j * ∏ k, y ⟨k, GenOnFibres.cellChart J k⟩ ^ (-a k)) + ℓ * v = 1

def ptCell : KH.Cell Unit PtIdx 0 :=
  ⟨fun _ => {0}, fun _ => Finset.singleton_nonempty _, by simp⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
