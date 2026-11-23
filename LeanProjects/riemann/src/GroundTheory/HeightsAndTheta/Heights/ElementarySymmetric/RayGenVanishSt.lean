import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsModelWithBase IsGenerated baseDeg pnPt isModelWithBase_pnPt
  veryAmple_pnPt)

def RayGenVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsModelWithBase F y k₀ → ∀ β : K → ℤ, IsGenerated F y β → ∀ e : K → ℤ,
      ∃ c₀ : ℕ, ∀ n c : ℕ, c₀ ≤ c →
        Subsingleton (cechHc ι (fun δ => quotPart F (mIdealOver F y) (δ + e)) (n • β + c • baseDeg k₀) 1)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
