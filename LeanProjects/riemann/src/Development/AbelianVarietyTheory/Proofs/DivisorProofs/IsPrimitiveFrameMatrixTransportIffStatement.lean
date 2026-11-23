import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂], IsLocIso j → ∀ (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → ∀ (Z : Matrix A D k), IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  first | exact @GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | exact GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | (intros; apply GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff <;> assumption)
