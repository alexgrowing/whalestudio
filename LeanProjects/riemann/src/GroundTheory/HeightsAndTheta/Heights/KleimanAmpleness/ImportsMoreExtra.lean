import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GenFibNef.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra F Ω] [IsScalarTower O F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (β : K → ℤ),
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O y)) β ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β

example (h : GenFibNef.Statement) :=
  h exO exF exΩ (Unit ⊕ Unit) (graphIdx 1 2) (graphVec (Kleiman.lineX exF) (Kleiman.lineX exF)) (graphDeg 0)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
