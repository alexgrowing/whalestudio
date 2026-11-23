import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_of_induced_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  first | exact @GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | exact GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | (intros; apply GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration <;> assumption)
