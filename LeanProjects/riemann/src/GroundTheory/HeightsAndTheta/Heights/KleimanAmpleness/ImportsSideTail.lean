import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibresNef.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ β : K → ℤ,
      (IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O)
          (NumbersDVR.specialIdeal (mIdealOver O (segreJoin y))) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O)
          (NumbersDVR.specialIdeal (mIdealOver O y)) β) ∧
      (IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O (segreJoin y)))
          (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib (mIdealOver O y)) β)

theorem SegreFibresNef.hyps :
    ∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX exF) ⟨k, i⟩ ≠ 0 :=
  fun _ => ⟨0, Kleiman.lineX_ne_zero exF 0⟩

example (h : SegreFibresNef.Statement) :=
  h exO exΩ Unit (fun _ => Fin (1 + 1)) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX exF)) SegreFibresNef.hyps 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
