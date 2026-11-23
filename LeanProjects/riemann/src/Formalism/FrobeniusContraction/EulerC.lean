import Formalism.FrobeniusContraction.StatementTop

noncomputable section

namespace Formalism.WachCohomologyFacts.Top2

def EulerC : Prop :=
  ∀ (K D : Type) [Field K] [AddCommGroup D] [Module K D] (v φ γ : D →ₗ[K] D)
    (N B G : Submodule K D) (A : ℕ),
    Function.Injective v → (∀ x, φ (γ x) = γ (φ x)) →
    N ≤ B → (∀ x ∈ N, φ x ∈ B) → (∀ x ∈ N, γ x - x ∈ G) →
    (∀ y ∈ B, γ y - y ∈ B.map v) → (∀ z ∈ G, φ z - z ∈ B.map v) →
    N.map (v ^ (A + 1)) ≤ G → G ≤ N.map v →
    (∀ x ∈ N.map (v ^ A), φ x ∈ N.map (v ^ A)) →
    (∀ y ∈ N.map (v ^ A), ∃ x ∈ N.map (v ^ A), φ x - x = y) →
    (∀ x ∈ N.map (v ^ A), φ x = x → x = 0) →
    (∀ x ∈ N.map (v ^ (A + 1)), φ x ∈ N.map (v ^ (A + 1))) →
    (∀ y ∈ N.map (v ^ (A + 1)), ∃ x ∈ N.map (v ^ (A + 1)), φ x - x = y) →
    (∀ x ∈ N.map (v ^ (A + 1)), φ x = x → x = 0) →
    (∀ x ∈ N.map (v ^ A), γ x - x ∈ N.map (v ^ (A + 1))) →
    Module.length K (↥N ⧸ (N.map (v ^ A)).comap N.subtype) < ⊤ →
    Module.length K (↥B ⧸ N.comap B.subtype) < ⊤ →
    let Z0 : Submodule K D := N ⊓ LinearMap.ker (φ - 1) ⊓ LinearMap.ker (γ - 1)
    let C1 : Submodule K (D × D) := B.prod G
    let d1 : D × D →ₗ[K] D := (γ - 1).coprod (-(φ - 1))
    let Z1 : Submodule K (D × D) := C1 ⊓ LinearMap.ker d1
    let B1 : Submodule K (D × D) := N.map ((φ - 1).prod (γ - 1))
    let vB : Submodule K D := B.map v
    let vN : Submodule K D := N.map v
    let h0 := Module.length K ↥Z0
    let h1 := Module.length K (↥Z1 ⧸ B1.comap Z1.subtype)
    let h2 := Module.length K (↥vB ⧸ (C1.map d1).comap vB.subtype)
    h0 < ⊤ ∧ h1 < ⊤ ∧ h2 < ⊤ ∧
      h0 + h2 = h1 + Module.length K (↥vN ⧸ G.comap vN.subtype) ∧
      N.map (v ^ (A + 1)) ≤ C1.map d1

def IneqI : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    Formalism.WachCohomologyFacts.Top.sg f ℓ h i < (ℓ : ℤ) * (Formalism.WachCohomologyFacts.Top.sg f ℓ h (i + 1) + 1) - h i

end Formalism.WachCohomologyFacts.Top2
