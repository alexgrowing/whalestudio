import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KCoinvOfNarrow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SoCoinvOfNarrow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMultiplicityOneIrreducibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCharOfCondLE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace PositivityTheory.BernsteinRamification

def NarrowBern : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

theorem narrowBern (hG : GlobalTheory.Published.GeometricLemmaFiltration) : NarrowBern :=
  GlobalTheory.CompanionTheory.SmGL.Bernstein.prod₂_detRep_isIrreducible hG

theorem kCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hD : PositivityTheory.KCo.DictSt) : GlobalTheory.ThK.KCoinv :=
  GlobalTheory.CompanionTheory.KCoNarrow.kCoinv_of_narrow (narrowBern hG) hD

theorem soCoinv_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hK : GlobalTheory.ThK.KFin) : PositivityTheory.ThKF.SoCoinv :=
  GlobalTheory.CompanionTheory.SoCoinvNarrow.soCoinv_of_narrow (narrowBern hG) hK

theorem ramifiedMultiplicityOne_of_geometricFiltration (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne :=
  GlobalTheory.CompanionTheory.BernNarrow.first_cohomology_ramified_narrow (narrowBern hG)

theorem finRam_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinRam :=
  GlobalTheory.CompanionTheory.SplitNarrow.finRam_of_narrow (narrowBern hG)

theorem finSplit_of_geo (hG : GlobalTheory.Published.GeometricLemmaFiltration) : PositivityTheory.ThK.FinSplit :=
  GlobalTheory.CompanionTheory.BernBridge.Split.finSplit_of_narrow (narrowBern hG)

end PositivityTheory.BernsteinRamification
