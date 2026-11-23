import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.SemisimpleDecompositionOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitBoundOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2TopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.SetPtOff

theorem litBurnside_all (D : D7) : LitBurnside (G D.host.E D.nd.Om) := by
  intro l _ a ρ h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact Subsingleton.elim _ _
  · apply GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ
    refine ⟨?_, ?_, ?_⟩
    · intro hb
      have : (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l)) := trivial
      rw [hb, Submodule.mem_bot] at this
      have h1 := congrFun this ⟨0, ha⟩
      simp at h1
    · intro g x _; trivial
    · intro W' _ hW'
      exact h W' (fun g _ x hx => hW' g x hx)

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ
  have fa := hS.facts
  have hHub := GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by linarith [hS.big]) le_rfl (by exact_mod_cast (Real.exp_pos _).le) (fa.admJ L hS.par) hS.par67 fa.admA
    fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1 fa.large.2.2 fa.nct fa.trip fa.same fa.block
    fa.muUnr fa.depthG
  have hR : RestPt i (X.r i) (X.ρ i) π := hHub.2.2.2.2.2.2.2.1 i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hJ := GlobalTheory.JumpStatement.holds_all D L (fa.admJ L hS.par)
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π :=
    semisimple_decomposition_of D i (X.r i) (X.ρ i) π fa.admA.2.2.2.2.2.2 hR.good hR.rho hR.ss
  exact ⟨galois_condition_one_of D i (X.r i) fa.Conclusion1.1 hR.good,
    GlobalTheory.GTwoTheta.main hP.font D L fa.g2.1 hJ.1 hJ.2.2.1 i (X.r i) (X.ρ i) π hR.good hR.ng0 hR.ng1 hZ hdec,
    galois_condition_three_of D i (X.r i) (X.ρ i) π fa.Conclusion1.1 hR.good hdec hR.cont hHG fa.rhoBar (litBurnside_all D) hR.g3,
    galois_condition_four_of D i (X.r i) fa.Conclusion1.1 hR.good,
    galois_condition_five_of D i (X.r i) fa.Conclusion2.1 hHG hR.good,
    (GlobalTheory.TameDesign.main D i).2,
    galois_condition_six_of D i (X.r i) fa.Conclusion2.2.1 hHG hR.good,
    GlobalTheory.T.blochKato_localCondition_all_localizations hP.bk hP.tate hP.euler D i,
    continuous_family_of D i (X.r i) hR.good,
    semisimple_family_of D i (X.r i) hR.good,
    hdec, hR.eps, GlobalTheory.T.completion_comparison_admissible_every_place_over D i, hR.shape, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i,
    GlobalTheory.T.integral_tate_H2_top hP.tate D i, GlobalTheory.T.unramifiedClassFieldBound_of_artin hP.artin D i⟩

end GlobalTheory.SetPtOff
