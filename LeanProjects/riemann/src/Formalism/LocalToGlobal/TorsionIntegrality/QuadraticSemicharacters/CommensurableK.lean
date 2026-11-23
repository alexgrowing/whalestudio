import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.InterIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Objects

variable {n k : Type*}

def blkSum (h₁ : Matrix n n ℂ) (h₂ : Matrix k k ℂ) : Matrix (n ⊕ k) (n ⊕ k) ℂ := Matrix.fromBlocks h₁ 0 0 h₂

def prodLat (Λ₁ : AddSubgroup (n → ℂ)) (Λ₂ : AddSubgroup (k → ℂ)) : AddSubgroup (n ⊕ k → ℂ) where
  carrier := {z | (fun i => z (Sum.inl i)) ∈ Λ₁ ∧ (fun j => z (Sum.inr j)) ∈ Λ₂}
  zero_mem' := ⟨Λ₁.zero_mem, Λ₂.zero_mem⟩
  add_mem' := fun ha hb => ⟨Λ₁.add_mem ha.1 hb.1, Λ₂.add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨Λ₁.neg_mem ha.1, Λ₂.neg_mem ha.2⟩

def tensFn (θ₁ : (n → ℂ) → ℂ) (θ₂ : (k → ℂ) → ℂ) (z : n ⊕ k → ℂ) : ℂ :=
  θ₁ (fun i => z (Sum.inl i)) * θ₂ (fun j => z (Sum.inr j))

end Objects

def ProdIntAt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (lg ph : PowerSeries ℂ_[l]), PowerSeries.constantCoeff lg = 0 →
    PowerSeries.constantCoeff ph = 0 → ∀ (n k : Type) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] (h₁ : Matrix n n ℂ) (h₂ : Matrix k k ℂ)
      (Λ₁ : AddSubgroup (n → ℂ)) (Λ₂ : AddSubgroup (k → ℂ)) (B₁ : Matrix n n ℂ_[l]) (B₂ : Matrix k k ℂ_[l])
      (θ₁ : (n → ℂ) → ℂ) (θ₂ : (k → ℂ) → ℂ),
      AnalyticOnNhd ℂ θ₁ Set.univ → AnalyticOnNhd ℂ θ₂ Set.univ →
      IntAt l ι lg ph h₁ Λ₁ B₁ θ₁ → IntAt l ι lg ph h₂ Λ₂ B₂ θ₂ →
      IntAt l ι lg ph (blkSum h₁ h₂) (prodLat Λ₁ Λ₂) (Matrix.fromBlocks B₁ 0 0 B₂) (tensFn θ₁ θ₂)

def CommensurableK : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n]
    [DecidableEq n] (Λ : AddSubgroup (n → ℂ)),
    relIdx (stdLat (cmL a b d ha hd lam hlam) n) Λ ≠ 0 → relIdx Λ (stdLat (cmL a b d ha hd lam hlam) n) ≠ 0 →
    ∀ g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
      (∀ w w', InK d (g (Pi.single w' 1) w)) → (∀ w w', InK d (g.symm (Pi.single w' 1) w)) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
          (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 ∧
        relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
          (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0

end Formalism.L2.Th1.H
