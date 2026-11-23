import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeTor

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E.E3

theorem sizet_holds : SizeT := by
  intro E _ _ _ N Q₁ Q₂ h₁ h₂
  obtain ⟨hcpt, -, -, c, hc⟩ :=
    GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E N
  obtain ⟨r₁, hr₁⟩ := hcpt Q₁ h₁
  obtain ⟨r₂, hr₂⟩ := hcpt Q₂ h₂
  have htor := GlobalTheory.CompanionTheory.TorNorm.torNorm GlobalTheory.CompanionTheory.LogAbs.logAbsBasic E
  have hd : (0 : ℝ) ≤ 2 * Module.finrank ℚ E := by positivity
  refine ⟨|r₁| + |r₂| + 2 * |c| + 2 * Module.finrank ℚ E, by positivity, fun q₁ hq₁ q₂ hq₂ x => ?_⟩
  have e₁ := hc (q₁ * An.tor E x) q₂
  have e₂ := hc q₁ (An.tor E x)
  have e₃ := (htor.2 N x).2
  have a₁ := (hr₁ q₁ hq₁).trans (le_abs_self r₁)
  have a₂ := (hr₂ q₂ hq₂).trans (le_abs_self r₂)
  have a₃ := le_abs_self c
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have m₁ : 0 ≤ (|r₁| + |r₂| + 2 * |c|) * ‖x‖ := mul_nonneg (by positivity) hx
  nlinarith

end PositivityTheory.Rg.BcB.E.E3

end
