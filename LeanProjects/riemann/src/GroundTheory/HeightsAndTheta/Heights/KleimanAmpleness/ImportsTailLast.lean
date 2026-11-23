import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def SpecialCurvesDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
      ∀ W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)), NumbersDVR.IsMultiProjPrime W →
        NumbersDVR.specialIdeal (mIdealOver O y) ≤ W →
          relDim (baseComap (IsLocalRing.ResidueField O) k₀ e W) = relDim W

theorem SpecialCurvesDim.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      NumbersDVR.IsMultiProjPrime (NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1))) ∧
      NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) ≤
        NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) :=
  ⟨SpecialCurves.hyps.1, SpecialCurves.hyps.2.1, le_rfl⟩

example (h : SpecialCurvesDim.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () 1
    (Equiv.refl _) SpecialCurvesDim.hyps.1 _ SpecialCurvesDim.hyps.2.1 SpecialCurvesDim.hyps.2.2

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
