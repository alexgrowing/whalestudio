import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondCoordinateOfOrthogonalSelfDual
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    (∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ Λ, a • l ∈ Λ) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F) →
    ∀ u : κ → Fv F v, (∀ y, ((0 : κ → Fv F v), y) ∈ Λ → ψ₀ (u ⬝ᵥ y) = 1) → ∃ y', (u, y') ∈ Λ := by
  first | exact @GlobalTheory.selfDual_exists_snd_of_orth | exact GlobalTheory.selfDual_exists_snd_of_orth | (intros; apply GlobalTheory.selfDual_exists_snd_of_orth <;> assumption)
