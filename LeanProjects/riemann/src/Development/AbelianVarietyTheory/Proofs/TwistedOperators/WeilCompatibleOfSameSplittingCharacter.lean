import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionIntertwinesWeilUpToCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittTowerRestrictionWeilCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionWeilCharacterRationalEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPlaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameCharCompat

theorem compatibleOfSameChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.CompatibleOfSameChar D := by
  intro D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ h f hf
  obtain ⟨c, hc⟩ := GlobalTheory.T.wittTowerRestriction_intertwines_weil_upToCharacter D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ
  have h1 : ∀ g, c g = 1 := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D W c
    (GlobalTheory.T.continuous_wittTowerRestriction_weilCharacter D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ c hc)
    (GlobalTheory.T.wittTowerRestriction_weilCharacter_rational_eq_one D V V' W r C B hs ψ χS χT χS χT' ω ω' hω hω' μ 𝓨 hμ c hc)
    (GlobalTheory.T.restriction_weilData_twistCharacter_trivial_splitPlaces D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ c hc)
  rw [hc h f hf, h1 h]
  simp

end GlobalTheory.SameCharCompat
