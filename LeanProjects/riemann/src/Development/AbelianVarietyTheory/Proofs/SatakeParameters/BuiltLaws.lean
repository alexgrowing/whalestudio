import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLawsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocCoincide

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem built_laws : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.HeightCounting.NBuilt hL D →
    GlobalTheory.RowTie.CharLaws D.nd D.naut ∧
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) ∧
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') := by
  intro hL D b
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.RowLaws.main _ _ _ _ _ A.wdT).2.1
  · intro i i' σ v _
    exact (Au.locW i σ v).trans (Au.locW i' σ v).symm
  · intro i i' hj hw
    have hj' : L.X.nd.j i = L.X.nd.j i' := hj
    have hw' : L.X.nd.w i = L.X.nd.w i' := hw
    have hjr : 1 ≤ L.X.nd.j i ∧ L.X.nd.j i ≤ D0.R.m := L.X.nd.j_range i
    have hmu : L.X.nd.mu i = L.X.nd.mu i' :=
      (L.X.nd.mu_w i).trans ((congrArg _ hw').trans (L.X.nd.mu_w i').symm)
    have e1 : L.X.nd.j i - 1 + 1 = L.X.nd.j i := by omega
    have e2 : L.X.nd.j i - 1 + 1 = L.X.nd.j i' := by omega
    have h1 := Au.muC i ⟨L.X.nd.j i - 1, by omega⟩ e1
    have h2 := Au.muC i' ⟨L.X.nd.j i - 1, by omega⟩ e2
    show L.Y.muC i = L.Y.muC i'
    apply A.chr.e1.injective
    apply Subtype.ext
    exact h1.trans ((congrArg (fun μ => tp.tup μ ⟨L.X.nd.j i - 1, by omega⟩) hmu).trans h2.symm)

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (M : Formalism.L2.MtFam D), GlobalTheory.HeightCounting.NBuilt hL D →
    Formalism.L2.HeckeTied D M → KillingConditions.LocalisationUniqueness D := fun hL D M b hT =>
  have h := built_laws hL D b
  GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws D M hT h.1 h.2.1 h.2.2

end GlobalTheory.LocCoincide

end
