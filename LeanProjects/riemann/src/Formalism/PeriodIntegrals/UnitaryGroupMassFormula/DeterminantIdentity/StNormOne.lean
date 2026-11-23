import Mathlib
import Formalism.PeriodIntegrals.DetIdPG

open NumberField

noncomputable section

namespace PI.DIP

def detId (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}

def IsLat (E : Type) [Field E] [NumberField E] (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤

def StAdj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    DetIdPG.IsSDLat E N L₀ → DetIdPG.IsSDLat E N L → ∀ x ∈ detId E N L₀ L, star x ∈ detId E N L L₀

def StProdLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    IsLat E N L₀ → IsLat E N L → detId E N L₀ L * detId E N L L₀ ≤ 1

def StProdGe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    IsLat E N L₀ → IsLat E N L → 1 ≤ detId E N L₀ L * detId E N L L₀

def StScal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)) (s : ℕ),
    (∀ x ∈ L₀, (s : E) • x ∈ L) → (s : E) ^ N ∈ detId E N L₀ L

def StNormOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}

def StIntNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ψ : E →+* ℂ_[p]) (x : 𝓞 E),
    ‖ψ (x : E)‖ ≤ 1

end PI.DIP
