import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocalSchwartzIntertwine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_schwartz_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ₀ : AddChar k ℂ),
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ₀ (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (c b a' : ℕ)
    (S : (Matrix (Fin a') (Fin (b + 2 + a')) k → ℂ) → Matrix (Fin a') (Fin (b + a')) k → ℂ),
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ g ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ z : ℂ,
      S (z • f + g) = z • S f + S g) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ r : Fin a' → k,
      S (fun Z => f (Z + Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1))) = S f) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ s : Fin a' → k,
      S (fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z (Matrix.vecMulVec s (Pi.single 0 1))) * f Z) = S f) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ Y : Matrix (Fin a') (Fin (b + a')) k,
      S (fun Z => f (Z + Y * (insP k b a')ᵀ)) = fun Z => S f (Z + Y)) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ Y : Matrix (Fin a') (Fin (b + a')) k,
      S (fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z (Y * (insP k b a')ᵀ)) * f Z) = fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z Y) * S f Z) →
    S (Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[k]} 1) = Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[k]} 1 →
    stdB ν ϖ c (b + 2) a' ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k) →
    S (stdB ν ϖ c (b + 2) a') = ((Nat.card 𝓀[k] : ℂ) ^ (-((c * a' : ℕ) : ℤ))) • stdB ν ϖ c b a' := by
  first | exact @GlobalTheory.EvZeroStd.map_stdB | exact GlobalTheory.EvZeroStd.map_stdB | (intros; apply GlobalTheory.EvZeroStd.map_stdB <;> assumption)
