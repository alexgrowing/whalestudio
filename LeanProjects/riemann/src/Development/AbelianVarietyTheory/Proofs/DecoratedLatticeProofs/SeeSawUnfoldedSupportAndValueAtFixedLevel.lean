import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymCollapseOfAllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllPositionsHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawLaws

open GlobalTheory.LocMod

theorem gsupp2_all (D : D7) : GlobalTheory.LocMod.GSupp2 D := by
  have hFL : FlatLaw D := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs : GlobalTheory.FinPl.FlatLaws D := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hOm : OmLoc D := GlobalTheory.T.weilDatum_localModel_formula D
  have hBF : FlatBF D := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB : FlatFB D := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hC : ContrLoc D := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hS : GlobalTheory.LocFlat.SymCollapse := GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds
  intro k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  exact GlobalTheory.T.support_levelPlace_symmetricChain_secondHalf D hOm hBF hFB hC hS k p s κ S t ψ s₁.weil.std hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne

theorem gsupp1_all (D : D7) : GlobalTheory.LocMod.GSupp1 D :=
  GlobalTheory.T.flat_map_support_first_half_at_level_place D (GlobalTheory.T.weilDatum_localModel_formula D)
    (GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D))
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds)

theorem gLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  obtain ⟨a, ha, hval⟩ := GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel D c v n G hc hv hG
  refine ⟨a, ha, fun t ht hW hch => ⟨?_, hval t ht hW⟩⟩
  have hs : GSupp (t := t) v :=
    GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces D c v n G hc hv hG (gsupp1_all D) (gsupp2_all D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) t ht hch
  exact hs

end GlobalTheory.SeeSawLaws
