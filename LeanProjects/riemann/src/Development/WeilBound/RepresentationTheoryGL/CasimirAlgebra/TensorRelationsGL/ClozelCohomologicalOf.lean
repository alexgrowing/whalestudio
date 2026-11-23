import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct Classical

namespace PositivityTheory.Rg.Cz

def kap (E : Type) [Field E] [NumberField E] (a : ℕ) (τ : E →+* ℂ) (k : Kinf E a) : Matrix (Fin a) (Fin a) ℂ :=
  k.1.map (coord τ)

abbrev barE (E : Type) [Field E] : (E →+* ℂ) → (E →+* ℂ) := NumberField.ComplexEmbedding.conjugate

def KData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
  IsKD (barE E) (kap E a) ∧ CompactSpace (Kinf E a)

def GKData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
  IsGK (barE E) (kap E a) (fun τ => cx τ (lieOp π)) (fun k => π.op (.cpt k))

def WhitLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
  ∃ ℓ : π.V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∀ τ, IsWh (cx τ (lieOp π)) ℓ

def CharInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
  (CG.mk π).IsRegAlg → ∃ l : (E →+* ℂ) → Fin a → ℤ, (∀ τ, Function.Injective (l τ)) ∧
    ∀ τ, HasChar (cx τ (lieOp π)) fun k => (l τ k : ℂ)

def IsUnitTw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a) : Prop :=
  ∃ (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (σ : ℝ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧
    ∀ (X : Lie E a) φ ψ, H (lieOp π X φ) ψ + H φ (lieOp π X ψ) = (σ * ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i)) * H φ ψ

def UnitTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
  IsUnitTw π

def IsSmall {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a) (Ξ : AlgRep E a) : Prop :=
  (∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) ∧
  ∀ τ : E →+* ℂ, ∃ c t : ℝ,
    (∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (c : ℂ)) ∧
    (∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (t : ℂ)) ∧
    (∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-t : ℂ)) ∧
    ∀ v : Fin Ξ.d → ℂ, (star v ⬝ᵥ ((∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i) *ᵥ v)).re ≤ c * (star v ⬝ᵥ v).re

def Coef : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
  (l : (E →+* ℂ) → Fin a → ℤ) (s : ℤ), (∀ τ, HasChar (cx τ (lieOp π)) fun k => (l τ k : ℂ)) →
  KTypeData (barE E) (kap E a) (fun k => π.op (.cpt k)) l s →
  ∃ (Ξ : AlgRep E a) (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
    IsSmall π Ξ ∧ IsCochain (tensorK π Ξ) ω ∧ ω ≠ 0

def Kuga : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a),
  IsUnitTw π → IsSmall π Ξ → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
    IsCochain (tensorK π Ξ) ω → ω ≠ 0 → IsCohFor π Ξ

theorem clozelCohomological_of (h1 : KType) (h2 : KData) (h3 : GKData) (h4 : WhitLie) (h5 : CharInt) (h6 : UnitTw)
    (h7 : Coef) (h8 : Kuga) : GlobalTheory.Published.ClozelCohomological := by
  intro E _ _ _ a ha π hr
  obtain ⟨hK, hc⟩ := h2 E a
  obtain ⟨ℓ, hℓ, hw⟩ := h4 E a π
  obtain ⟨l, hl, hch⟩ := h5 E a π hr
  obtain ⟨s, hs⟩ := h1 a ha π.V (E →+* ℂ) (Kinf E a) _ _ _ _ hK (h3 E a π) l hl hch ℓ hℓ hw
  obtain ⟨Ξ, q, ω, hΞ, hω, h0⟩ := h7 E a π l s hch hs
  exact ⟨Ξ, h8 E a π Ξ (h6 E a ha π) hΞ q ω hω h0⟩

end PositivityTheory.Rg.Cz

end
