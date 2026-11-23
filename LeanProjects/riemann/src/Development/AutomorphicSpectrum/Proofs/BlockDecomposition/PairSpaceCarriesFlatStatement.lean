import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlat

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_carries_flat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), FlatFn e₁ → FlatFn e₂ → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → F ∈ pairSpace U₁ U₂ → TypeH K₁ K₂ W₁ W₂ F → (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.pair_carry | exact GlobalTheory.CompanionTheory.LimV.pair_carry | (intros; apply GlobalTheory.CompanionTheory.LimV.pair_carry <;> assumption)
