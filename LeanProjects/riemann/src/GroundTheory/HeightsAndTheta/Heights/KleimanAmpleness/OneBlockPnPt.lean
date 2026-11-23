import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelCurvesLift.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
        mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
            baseComap F k₀ e W = P

theorem ModelCurvesLift.oneBlock_pnPt (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm) =
      IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1 := by
  funext ⟨⟨⟩, i⟩
  rfl

theorem ModelCurvesLift.hyps (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∧
      NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock
        (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm))) := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 1, ?_⟩
  rw [ModelCurvesLift.oneBlock_pnPt, IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt]
  exact NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
