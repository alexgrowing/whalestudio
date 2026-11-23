import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.KSplit

namespace GlobalTheory.JacLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk3 (a b : ℕ) : Fin 1 ⊕ Fin (a + b) ⊕ Fin 1 ≃ Fin (a + (b + 2)) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def IsJacMap (a b : ℕ) (α β : kˣ →* ℂˣ) (χ₁ χ₂ : kˣ → ℂ) (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : Prop :=
  (∀ (u : GL (Fin (a + (b + 2))) k) (X : Matrix (Fin 1) (Fin (a + b) ⊕ Fin 1) k) (Y : Matrix (Fin (a + b)) (Fin 1) k),
      u.val.submatrix (blk3 a b) (blk3 a b) = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * u)) →
        φ f₁ = φ f) ∧
  ∀ (m : GL (Fin (a + (b + 2))) k) (x y : kˣ) (g : GL (Fin (a + b)) k),
      m.val.submatrix (blk3 a b) (blk3 a b) =
        fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * m)) →
        ∀ h, (φ f₁ : GL (Fin (a + b)) k → ℂ) h = χ₁ x * χ₂ y * (φ f : GL (Fin (a + b)) k → ℂ) (h * g)

end GlobalTheory.JacLine

end
