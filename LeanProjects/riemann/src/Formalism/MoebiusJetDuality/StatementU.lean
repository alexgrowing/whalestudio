import Formalism.MoebiusJetDuality.StatementV
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.MJ

open Matrix
open scoped ComplexOrder

def blk {p q : ℕ} (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) : GL (Fin p ⊕ Fin q) ℂ where
  val := fromBlocks (A : Matrix (Fin p) (Fin p) ℂ) 0 0 (D : Matrix (Fin q) (Fin q) ℂ)
  inv := fromBlocks ((A⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0
    ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

def moeb {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * z + g.toBlocks₁₂) * (g.toBlocks₂₁ * z + g.toBlocks₂₂)⁻¹

def hcDom (p q : ℕ) : Set (Matrix (Fin p) (Fin q) ℂ) :=
  {z | (1 - zᴴ * z).PosDef}

def vecOf {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : Fin p × Fin q → ℂ := fun x => z x.1 x.2

def moebiusJetDuality : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
      (A : Matrix (Fin p) (Fin p) ℂ) * z * ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)

def moebiusJetDualityReformulated : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ),
    blk A D ∈ Formalism.UG.Upq p q ↔
      ((A : Matrix (Fin p) (Fin p) ℂ)ᴴ * (A : Matrix (Fin p) (Fin p) ℂ) = 1 ∧
        (D : Matrix (Fin q) (Fin q) ℂ)ᴴ * (D : Matrix (Fin q) (Fin q) ℂ) = 1)

def StabZero : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ), g ∈ Formalism.UG.Upq p q →
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = 0 → g ∈ Formalism.UG.blockDiag p q

def MoebTangent : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    vecOf (moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) =
      (hcMat (A : Matrix (Fin p) (Fin p) ℂ) ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec
        (vecOf z)

def ActFMoeb : Prop :=
  ∀ (p q r : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ))
    (z : Matrix (Fin p) (Fin q) ℂ),
    actF ρ k F (vecOf z) = ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
      (F (vecOf (moeb (((blk k.1 k.2)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)))

def MoebDom : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      IsUnit ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂).det ∧
      moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q

def MoebMul : Prop :=
  ∀ (p q : ℕ) (g h : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → h ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      moeb ((g * h : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
        moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
          (moeb (h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)

def ZeroMemDom : Prop := ∀ p q : ℕ, (0 : Matrix (Fin p) (Fin q) ℂ) ∈ hcDom p q

end Formalism.MJ
