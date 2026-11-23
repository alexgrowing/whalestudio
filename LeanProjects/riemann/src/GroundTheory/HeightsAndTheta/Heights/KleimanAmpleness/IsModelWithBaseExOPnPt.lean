import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def SpecialCurves.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra (FractionRing O) Ω] [IsScalarTower O (FractionRing O) Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω),
    x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase O y k₀ →
      ∀ d : ℕ,
        (∀ W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)), NumbersDVR.IsMultiProjPrime W →
          NumbersDVR.specialIdeal (mIdealOver O y) ≤ W → relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) →
            NumbersDVR.IsMultiProjPrime (baseComap (IsLocalRing.ResidueField O) k₀ e W) ∧
              NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤
                baseComap (IsLocalRing.ResidueField O) k₀ e W ∧
              relDim (baseComap (IsLocalRing.ResidueField O) k₀ e W) = ((d : ℕ) : WithBot (WithTop ℤ))) ∧
        (∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) (IsLocalRing.ResidueField O)),
          NumbersDVR.IsMultiProjPrime P →
          NumbersDVR.specialIdeal (mIdealOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ≤ P →
          relDim P = ((d : ℕ) : WithBot (WithTop ℤ)) →
            ∃ W : Ideal (NumbersDVR.MRing ι (IsLocalRing.ResidueField O)), NumbersDVR.IsMultiProjPrime W ∧
              NumbersDVR.specialIdeal (mIdealOver O y) ≤ W ∧ relDim W = ((d : ℕ) : WithBot (WithTop ℤ)) ∧
              baseComap (IsLocalRing.ResidueField O) k₀ e W = P)

theorem mIdealOver_exO_pnPt : mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hcomp : ((MvPolynomial.aeval (R := IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1)
      (fun _ : Unit => (1 : IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1))).restrictScalars exO).comp
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) =
      (IsScalarTower.toAlgHom exO (MvPolynomial (Σ k, IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1 k) exF)
        (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1)).comp (MvPolynomial.mapAlgHom (Algebra.ofId exO exF)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.pnPt]
  have h1 := AlgHom.congr_fun hcomp f
  have hf' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) f = 0 := hf
  rw [AlgHom.comp_apply, hf', map_zero, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at h1
  have h2 : MvPolynomial.mapAlgHom (Algebra.ofId exO exF) f = 0 :=
    (IsFractionRing.injective _ (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1)) (by rw [← h1, map_zero])
  have hinj : Function.Injective (MvPolynomial.map (σ := Σ k, IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1 k)
      (algebraMap exO exF)) := MvPolynomial.map_injective _ (IsFractionRing.injective exO exF)
  exact hinj (by simpa [MvPolynomial.mapAlgHom_apply] using h2)

theorem isModelWithBase_exO_pnPt : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () :=
  ⟨fun _ => ⟨0, IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero exF 1 _⟩, rfl⟩

theorem specialIdeal_exO_pnPt :
    NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1)) = ⊥ := by
  rw [mIdealOver_exO_pnPt, NumbersDVR.specialIdeal, Ideal.map_bot]

theorem SpecialCurves.hyps :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () ∧
      NumbersDVR.IsMultiProjPrime (NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1))) ∧
      relDim (NumbersDVR.specialIdeal (mIdealOver exO (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1))) =
        ((1 : ℕ) : WithBot (WithTop ℤ)) := by
  refine ⟨isModelWithBase_exO_pnPt, ?_, ?_⟩
  · rw [specialIdeal_exO_pnPt]
    exact NumbersDVR.isMultiProjPrime_bot
  · rw [specialIdeal_exO_pnPt]
    exact GroundTheory.Heights₂.Heights.FieldNumbers.relDim_projectiveSpace 1

example (h : SpecialCurves.Statement) :=
  h exO Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 1) (IndefiniteRowSideFullHecke.Kleiman2.pnField exF 1) (IndefiniteRowSideFullHecke.Kleiman2.pnPt exF 1) () 1
    (Equiv.refl _) _ rfl SpecialCurves.hyps.1 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
