import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable def baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (W : Ideal (NumbersDVR.MRing ι F)) : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F) :=
  W.comap (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k))

def ModelCurves.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ d : ℕ,
        (∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
          relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) →
            NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) ∧
              mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W ∧
              relDim (baseComap F k₀ e W) = ((d : ℕ) : WithBot (WithTop ℤ))) ∧
        (∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
          mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P → relDim P = ((d : ℕ) : WithBot (WithTop ℤ)) →
            ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
              relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) ∧ baseComap F k₀ e W = P)

theorem ModelCurves.hyps (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∧
      NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) ∧
      relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) = ((1 : ℕ) : WithBot (WithTop ℤ)) ∧
      baseComap F () (Equiv.refl (Fin (1 + 1))) (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1)) = ⊥ := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 1, ?_, IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 1, ?_⟩
  · rw [IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt]
    exact NumbersDVR.isMultiProjPrime_bot
  · rw [IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt, baseComap]
    refine Ideal.comap_bot_of_injective _ (rename_injective _ ?_)
    rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
    simpa using h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
