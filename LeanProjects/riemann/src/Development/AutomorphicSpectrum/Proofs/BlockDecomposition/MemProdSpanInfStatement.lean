import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prodSpan_inf : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ)) (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ → (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) → G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | exact GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | (intros; apply GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices <;> assumption)
