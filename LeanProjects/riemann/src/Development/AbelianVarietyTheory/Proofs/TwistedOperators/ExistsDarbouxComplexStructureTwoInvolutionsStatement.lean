import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDarbouxComplexStructureTwoInvolutions
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_complex_structure_two_involutions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (θA : InfinitePlace F → Matrix α α ℂ)
    (θB : InfinitePlace F → Matrix β β ℂ) (ε ε' : InfinitePlace F → ℤˣ), IsCMExt F E σ →
    (∀ w, θA w * θA w = 1) → (∀ w, θB w * θB w = 1) →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ u u' u₁ : Matrix α β (AE F E),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧
        (∀ w, u'.map (piInf (τ w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        (∀ w, u₁.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θA w * u.map (piInf (τ w)) * (θB w)ᵀ)) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.SignInvolDarboux.exists_bridge | exact GlobalTheory.SignInvolDarboux.exists_bridge | (intros; apply GlobalTheory.SignInvolDarboux.exists_bridge <;> assumption)
