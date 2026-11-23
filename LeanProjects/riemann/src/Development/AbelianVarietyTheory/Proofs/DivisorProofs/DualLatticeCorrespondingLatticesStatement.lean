import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLattices
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_correspondingLattices : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [Fintype D] [Fintype D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.dualLat_latCorr | exact GlobalTheory.PureMatch.Transport.dualLat_latCorr | (intros; apply GlobalTheory.PureMatch.Transport.dualLat_latCorr <;> assumption)
