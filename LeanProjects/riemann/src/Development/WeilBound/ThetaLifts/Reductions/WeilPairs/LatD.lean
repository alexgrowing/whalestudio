import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def LatO (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ L : Submodule (𝓞 E) (Fin n → E), L.IsLattice E ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)

def LatD (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ L : Submodule (𝓞 E) (Fin n → E), L.IsLattice E ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))

def Lat (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) : Prop :=
  LatO σ JTᵀ ∧ LatD σ (-(ξ₀ • JS⁻¹))

end PositivityTheory.ThKW

end
