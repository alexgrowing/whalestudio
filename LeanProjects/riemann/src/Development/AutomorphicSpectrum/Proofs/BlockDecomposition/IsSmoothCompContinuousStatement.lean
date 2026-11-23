import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuous
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmooth_comp_continuous : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G), Continuous ψ → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | exact GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | (intros; apply GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp <;> assumption)
