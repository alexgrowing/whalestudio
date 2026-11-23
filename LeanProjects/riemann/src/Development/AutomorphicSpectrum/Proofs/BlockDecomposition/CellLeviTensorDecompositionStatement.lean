import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellLeviTensorDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_levi_tensor_decomposition : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c c' : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] [∀ i j, Fintype (c' i j)] [∀ i j, DecidableEq (c' i j)], (∀ i j, Fintype.card (c i j) = Fintype.card (c' i j)) → ∀ (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (f' : ∀ i, (Σ j, c' i j) ≃ m i) (g' : ∀ j, (Σ i, c' i j) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((cellFunctor f g ρ).Equiv (cellFunctor f' g' ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.CellCongr.cellFunctor_congr | exact GlobalTheory.CompanionTheory.CellCongr.cellFunctor_congr | (intros; apply GlobalTheory.CompanionTheory.CellCongr.cellFunctor_congr <;> assumption)
