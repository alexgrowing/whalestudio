import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPatternStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOneStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem atMostOne_holds : AtMostOne := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hclass : S.OneClass t ν := GlobalTheory.T.symmetricChain_oneLatticeClass k ν hν s κ S t
  have hsupp : S.SupportOne t := GlobalTheory.T.symmetricChain_supportOne_of_pattern k s κ S t hpat
  exact ⟨GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricChain_projected_level_of_pattern k s κ S t hpat, GlobalTheory.T.symmetricChain_oneCoupling_coset_of_pattern k s κ S t hpat⟩

end GlobalTheory.SymChain
