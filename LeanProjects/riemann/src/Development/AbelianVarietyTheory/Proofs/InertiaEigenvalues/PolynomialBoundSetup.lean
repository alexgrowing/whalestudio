import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitBoundOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmJumpSetupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisLast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDualityStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.TheoremBQD

open MvPolynomial

def polyB : MvPolynomial (Fin 3) ℕ := 260 * X 0 ^ 2 * X 2 ^ 2 * (X 1 + X 2)

theorem polyB_val (f r t : ℕ) : 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal polyB f r t := by
  simp [EmbeddingTypeJumps.polyVal, polyB]

theorem exists_good {D : D7} {i : D.nd.Loc} (hi : EmbeddingTypeJumps.AtQD i) : ∃ π, π ∈ D.nd.Zgood i := by
  obtain ⟨π, hπ⟩ := hi.2
  exact ⟨π, (D.Zgood_tie i π).2 hπ⟩

theorem main_of (hc : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp) : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  refine ⟨2080, polyB, ?_⟩
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : (0 : ℝ) ≤ L.sc.b := (Real.exp_pos _).le
  have hX := GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by have := hS.big; linarith) le_rfl (by simpa using hb) (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  have hSet := GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hS
  have hpt : ∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := fun i hi π hπ =>
    hSet i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ
  obtain ⟨ep, hep⟩ := (GlobalTheory.JumpStatement.holds_all D L (hS.facts.admJ L hS.par)).1
  have hJ := GlobalTheory.T.admJump_setup hP D L P nch HW F Cm X C₂ hS ep hep
  have hSt := GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems hP.artin hP.bk hP.tate hP.euler D (GlobalTheory.DesignUnconditional.main D hS.facts.large.2.2)
  have hN5 : EmbeddingTypeJumps.GlobalIndexAwayFromTypes X.r X.ρ := fun i π dc lenRow e' cB hA =>
    hSt.1 i (X.r i) (X.ρ i) π dc lenRow e' cB (hX.1 i) hA
  have hKill : EmbeddingTypeJumps.KillingTwistedPlaces X.ρ := by
    intro i hl htw _ π hπ
    have hk := hS.kill i htw
    have h2 := UpperTheory.KStar.nuL_eq_zero_of_qd D _ hl
    refine ⟨?_, ?_⟩
    · have := (hk.1 π hπ).2
      simpa [h2, TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div] using this
    · simpa [TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div, EmbeddingTypeJumps.vZeta] using hk.2
  refine (hc hP.artin hP.bk hP.tate hP.euler D HW F Cm X.r X.ρ L ep 2080 polyB le_rfl polyB_val hN5
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).1)
    (fun i hi π hπ => (hpt i hi π hπ).2.1)
    (fun i hi π hπ => (hpt i hi π hπ).2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.2.1)
    (fun i hi π hπ => by
      obtain ⟨-, -, -, -, -, -, -, -, hc1, hs1, hd1, he1, -⟩ := hpt i hi π hπ
      exact ⟨hc1, hs1, hd1, he1⟩)
    hKill hJ hX.2.2.1
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.1)
    hS.par67).2.2

theorem main : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q :=
  main_of GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality

end GlobalTheory.TheoremBQD

end
