import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.PlaneSkew

variable {E : Type} [Field E] [NumberField E]

def lowLat {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n₁ → E) :=
  L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))

theorem mem_lowLat {n n₁ : ℕ} {ι : Matrix (Fin n) (Fin n₁) E} {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin n₁ → E} :
    u ∈ lowLat ι L ↔ ι *ᵥ u ∈ L := Iff.rfl

def PrimAt (𝔓 : HeightOneSpectrum (𝓞 E)) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) : Prop :=
  (∀ s : E, s • x ∈ L → 𝔓.valuation E s ≤ 1) ∧ ∃ s : E, s • x ∈ L ∧ 𝔓.valuation E s = 1

end GlobalTheory.PlaneSkew
