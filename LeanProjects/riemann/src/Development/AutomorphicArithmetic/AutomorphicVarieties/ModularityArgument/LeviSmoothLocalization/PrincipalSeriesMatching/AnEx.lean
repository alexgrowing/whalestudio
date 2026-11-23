import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.Loc2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.RsOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.EulOf

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem anEx : AnEx := by
  intro hp k N _ hk χ hχ g
  obtain ⟨hf, he⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨D, rfl, hs, hfe⟩ := Ad3.R.rs_of Ad3.loc2 k N hk χ hχ g.f g.a hf he (hp k N hk χ hχ g)
  rcases Ad3.S.anOf g.a D hfe (Ad3.S.eulOf Ad3.S.shim N χ D g.f g.a hf he hs) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨D, rfl, hs, h⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
