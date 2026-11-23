import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsModelWithBaseExOPnPt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SpecialCurvesLift.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω),
    x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) (IsLocalRing.ResidueField O)),
        NumbersDVR.IsMultiProjPrime P →
        NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)), NumbersDVR.IsMultiProjPrime W ∧
            NumbersDVR.specialIdeal (mIdealOver O y) ≤ W ∧
            baseComap (IsLocalRing.ResidueField O) k₀ e W = P

theorem SpecialCurvesLift.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      NumbersDVR.IsMultiProjPrime (NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.oneBlock
        (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm)))) := by
  refine ⟨SpecialCurves.hyps.1, ?_⟩
  rw [ModelCurvesLift.oneBlock_pnPt]
  exact SpecialCurves.hyps.2.1

example (h : SpecialCurvesLift.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () 1
    (Equiv.refl _) _ rfl SpecialCurvesLift.hyps.1 _ SpecialCurvesLift.hyps.2 le_rfl

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
