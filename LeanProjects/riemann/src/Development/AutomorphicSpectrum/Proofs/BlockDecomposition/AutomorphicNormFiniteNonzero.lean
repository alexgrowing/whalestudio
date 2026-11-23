import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqIntAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PosNorm

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem sqMass_ne_top_and_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
      ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 →
        (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ ⊤ ∧ (∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ) ≠ 0 := by
  intro E _ _ _ N _ _ μ _ F hF φ hA hS hne
  exact ⟨(GlobalTheory.CompanionTheory.SqIntFD.sqIntAt E N μ F hF φ hA hS).ne,
    (GlobalTheory.CompanionTheory.PosNormFD.posNorm E N μ F hF φ hA hS hne).ne'⟩

end GlobalTheory.CompanionTheory.FinDisc

end
