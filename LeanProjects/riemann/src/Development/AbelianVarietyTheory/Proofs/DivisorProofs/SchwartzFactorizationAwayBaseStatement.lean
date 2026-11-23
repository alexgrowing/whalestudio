import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizationAwayBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_factorization_away_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ v : Pl F, v ≠ B.v₁ → ∃ (N : ℕ) (ψ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) (r : Fin N → ((Fin a' × Fin (a + a') → AF F) → ℂ)), (∀ j, ψ j ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ j, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rest (evFin F v) φ (r j) ∧ tens (evFin F v) φ (r j) ∈ G.M'.So B.ψ B.τ₁) ∧ Φ = ∑ j, tens (evFin F v) (ψ j) (r j) := by
  first | exact @GlobalTheory.SoFactorAt.dec | exact GlobalTheory.SoFactorAt.dec | (intros; apply GlobalTheory.SoFactorAt.dec <;> assumption)
