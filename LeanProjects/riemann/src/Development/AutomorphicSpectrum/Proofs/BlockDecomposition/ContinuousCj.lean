import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwUFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem iwU_facts : P_iwU_facts := by
  intro E _ _ _ w hw n b hb ϖ l
  have hc : Continuous (cj w) := continuous_cj w
  exact ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc,
    ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b, GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b)
      (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc),
    GlobalTheory.CompanionTheory.IwLevels.isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwUFacts
