import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutBoundOfSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory

theorem conclusion_of_typeLocus {D : D7} (P : Pend D) (CT : ℕ)
    (hcut : ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs)
    (hl5 : CongruenceAtTypePrimes (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π)) :
    CongruenceAtTypePrimes (D := D) CT (CongruenceLocalDecomposition CT) := by
  intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  have hQ := hl5 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h6 h7 h8
  have hc := hcut i k hl
  choose! Xs β b hcb using hc
  refine ⟨Xs, β, b, fun π hπ => ⟨(hcb π hπ).1, ?_⟩⟩
  exact hQ π hπ (Xs π) (hcb π hπ).1.1 (hcb π hπ).2

theorem conclusion_of_admissibles : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → GaloisFamilyConditions (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → PairedCharacterCondition.aux₃ (D := D) C CT := by
  intro hGAR D P HW F C CT hC hadm5 hEig hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hSer hTB hBK hBC hLGC htie0 htieChi
  have hSteps : StepsNoCut := GlobalTheory.T.steps_of_artin_reciprocity hGAR
  have hCent : CentralElt D := hSteps.2.1 hSteps.1 D P
  have hl5 := GlobalTheory.Pass.cutBound_of_steps hSteps D P HW F CT hadm5 (GlobalTheory.Per.ResFinite.adm12_elementDenominator D) hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB
    hBK hBC hLGC (GlobalTheory.FontaineAdmissible.fontaineProperties_all_places D) htie0 htieChi
  have hcut := GlobalTheory.T.exists_type_locus D P hSer hBC hLGC htie0 hadm5 hEig hCent
  have h3 : CongruenceAtTypePrimes (D := D) CT (CongruenceLocalDecomposition CT) := conclusion_of_typeLocus P CT hcut hl5
  have h4 : CongruenceAtTypePrimes (D := D) CT (EtaBound CT) := by
    intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h6 h7 h8
    exact GlobalTheory.EtaFromCut.etaBound_of_cut D CT i k ρ eta
      (h3 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h6 h7 h8)
  exact GlobalTheory.typePrimeBound_of_etaBound D C CT hC h4

end GlobalTheory
