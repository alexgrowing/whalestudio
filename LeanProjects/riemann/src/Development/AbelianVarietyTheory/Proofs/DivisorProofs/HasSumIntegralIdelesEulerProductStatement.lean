import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProduct
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integralIdeles_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (S L : ℂ), UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → 1 < S.re → HasProd (eulerFactor χ S) L → open Classical in HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q) // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q)) = z ∧ (y : Af E) ∈ hatO (condQ 𝔣 Q)} => (finPart χ z.1.out : ℂ) * ((modF z.1.out : ℝ) : ℂ) ^ S) (L * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) + ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2)) := by
  first | exact @GlobalTheory.CMVal.Euler.hasSum_euler | exact GlobalTheory.CMVal.Euler.hasSum_euler | (intros; apply GlobalTheory.CMVal.Euler.hasSum_euler <;> assumption)
