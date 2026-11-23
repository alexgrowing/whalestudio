import Formalism.SubspaceCounting.Statement

noncomputable section

open scoped BigOperators

namespace Formalism.G0

def esymmR {V : ℕ} (κ : Fin V → ℝ) (k : ℕ) : ℝ :=
  ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard k, ∏ v ∈ B, κ v

def ManyOrbits : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (V : ℕ) (π : R), Irreducible π →
    ∀ (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m β₀ c₀ S d : ℕ) (a b c Sv : Fin V → ℕ) (κ : Fin V → ℝ)
    (G : Finset (Fin V) → Finset X),
    [Module.Free R (L fun _ => Slot.base)] → [Module.Finite R (L fun _ => Slot.base)] →
    Module.finrank R (L fun _ => Slot.base) = d →
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), B.card ≤ β₀ + 2 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ ((G B).card : ℝ) ≤ 2 * (∏ v ∈ B, κ v) * d ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, 0 ≤ κ v) → (∀ v, a v + b v ≤ c v) → (∀ v, Sv v ≤ S) →
    (m : ℝ) * ∑ v, κ v ≤ 1 / 2 →
    let M := L fun _ => Slot.base
    let N := prodIdealMap π y m Sv M
    let τ := ∑ v, m * (c v + c₀)
    (∀ β ≤ β₀ + 1, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
        (C.card : ℝ) ≤ 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d ∧
        ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X)) ∧
    AllButLE π M N 0 (∑ v, Sv v) ∧
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * (τ + 4 * S * (m * ∑ v, κ v) +
        V * S * (2 * (m * ∑ v, κ v) ^ (β₀ + 1) / (β₀ + 1).factorial))

def tailK {K : ℕ} (α : Fin K → ℕ) (u : ℕ) : ℕ :=
  ∑ l : Fin K, if u ≤ l.val then α l else 0

def VecStep {K : ℕ} (α α' : Fin K → ℕ) (B : ℕ) : Prop :=
  (∀ l, α l ≤ α' l) ∧ (∀ (l : Fin K) (h : l.val + 1 < K), α' ⟨l.val + 1, h⟩ ≤ α l) ∧
    ∑ l, α' l ≤ ∑ l, α l + B

def ShrinkStep {K : ℕ} (α α' : Fin K → ℕ) : Prop := ∀ l, α' l ≤ α l

def IsPath {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ) : Prop :=
  what₂ 0 = 0 ∧ ∀ (i : ℕ) (h : i < steps.length),
    match steps[i] with
    | some B => VecStep (what₂ i) (what₂ (i + 1)) B
    | none => ShrinkStep (what₂ i) (what₂ (i + 1))

def latestDegrees (steps : List (Option ℕ)) (i : ℕ) : List ℕ :=
  ((steps.take i).filterMap id).reverse

def TailSums : Prop :=
  ∀ {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ), IsPath steps what₂ →
    (∀ i ≤ steps.length, ∀ u, tailK (what₂ i) u ≤ ((latestDegrees steps i).drop u).sum) ∧
    (∀ i j u X, i ≤ j → j ≤ steps.length →
      tailK (what₂ i) u + X ≤ ((latestDegrees steps i).drop u).sum →
      let n := (((steps.drop i).take (j - i)).filterMap id).length
      tailK (what₂ j) (u + n) + X ≤ ((latestDegrees steps j).drop (u + n)).sum)

end Formalism.G0
