import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

def BundleRealises {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {x : Fin (N + 1) → Ω}
    (Q : Kleiman.LineBundle S x) (β : K → ℤ) : Prop :=
  ∀ c : ℤ, (Q.toSubSystem.twist (Kleiman.twistSys S x c)).secs =
    secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem realises_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    BundleRealises (graphVec x s) baseBlock Q (graphDeg n) :=
  fun c => twist_secs_eq_secOver Q n s hgen c

end Graph

section Point

variable (k : Type) [Field k]

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
