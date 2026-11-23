import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
import Development.WeilBound.CoreStatements.PublishedTheorems.PolarizedGaloisRepresentations.GaloisRepOfPolarizedPairLit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepOfPolarizedPairOfHyps
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace UpperTheory.GalN

theorem cusp_of_pair (hGK : GlobalTheory.Published.GelfandKazhdanDual) (hP : PairU) : CuspU := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
  exact hP E Ω l ι a ha π χ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

theorem bridge' : GlobalTheory.Published.GelfandKazhdanDual → (CarU → CarU) ∧ (PairU → CuspU) :=
  fun hGK => ⟨id, cusp_of_pair hGK⟩

end UpperTheory.GalN
