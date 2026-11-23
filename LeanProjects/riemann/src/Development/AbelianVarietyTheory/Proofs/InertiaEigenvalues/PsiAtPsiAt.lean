import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameCharEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValueStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

example : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C → GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := main

end GlobalTheory.JointSix

end
