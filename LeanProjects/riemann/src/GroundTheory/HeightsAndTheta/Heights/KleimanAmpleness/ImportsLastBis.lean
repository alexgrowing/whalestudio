import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SpecialModelPoint.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K), IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
    ∀ (Ω' : Type) [Field Ω'] [Algebra (IsLocalRing.ResidueField O) Ω'] (y' : (Σ k, ι k) → Ω'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) →
      NumbersDVR.specialIdeal (mIdealOver O y) ≤ mIdealOver (IsLocalRing.ResidueField O) y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase (IsLocalRing.ResidueField O) y' k₀

theorem SpecialModelPoint.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      (∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1 ⟨k, i⟩ ≠ 0) ∧
      NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) ≤
        mIdealOver (IsLocalRing.ResidueField exO) (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) := by
  refine ⟨isModelWithBase_exO_pnPt, fun _ => ⟨0, IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero _ 1 _⟩, ?_⟩
  rw [specialIdeal_exO_pnPt]
  exact bot_le

example (h : SpecialModelPoint.Statement) :=
  h exO (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) ()
    SpecialModelPoint.hyps.1 _ (IndefiniteRowSideFullHecke.Kleiman2.pnPt (IsLocalRing.ResidueField exO) 1) SpecialModelPoint.hyps.2.1
    SpecialModelPoint.hyps.2.2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
