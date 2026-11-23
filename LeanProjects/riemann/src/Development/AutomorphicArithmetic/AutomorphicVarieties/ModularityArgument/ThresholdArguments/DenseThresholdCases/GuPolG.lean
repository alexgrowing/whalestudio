import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompatiblePolarizationOfLink
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT :
    _root_.UpperTheory.V.Af.HypothesesH' → RowT → PolG := by
  intro PH hRow E Ω _ _ _ _ _ _ l _ ι a ha P χ hreg hpol σ hσ
  obtain ⟨r, wt, HT, H⟩ := hRow E Ω l ι a ha P χ hreg
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a P (compNorm E χ) (PH.toClassicalTheorems.litN.aut.gk E a _) hpol.dual⟩
  have hRc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w hg A h O _ _ _ Bw hj => ?_,
    fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj g => ?_⟩⟩, H.weights⟩
  · obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
    obtain ⟨g1, g2⟩ := hg A h rc hrc
    obtain ⟨k1, -, k3, -⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g1) g2
    exact ⟨k1, k3⟩
  · exact ⟨wdOf h hw ι r, isWDOf_wdOf hw ι hRc, fun g => (H.away w hw A h rc hrc (σ w) (hσ w)).tor g.1 g.2⟩
  · obtain ⟨-, k2, -, k4⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g.1) g.2
    exact ⟨k2, k4.tor g.1 g.2⟩
end
end
