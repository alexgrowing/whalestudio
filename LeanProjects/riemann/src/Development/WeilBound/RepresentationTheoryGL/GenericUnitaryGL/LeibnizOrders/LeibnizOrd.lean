import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.RgGu.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ResSeq : Prop :=
  ∀ (i j n : ℕ) (hn : i + j + 1 = n) (π₁ : GRep k (i + 1)) (π₂ : GRep k (j + 1)), IsSmooth π₁.ρ → IsSmooth π₂.ρ →
    MExt (mcast (by omega) (prodPGn (gres π₁) π₂)) (gres ((π₁.prod π₂).cast (by omega : (i + 1) + (j + 1) = n + 1)))
      (mcast (by omega) (prodGPn π₁ (gres π₂)))

def PsiGP : Prop :=
  ∀ (m j : ℕ) (ρ : GRep k m) (τ : MRep k j), IsSmooth ρ.ρ → IsSmooth τ.ρ → GIso (psiN (prodGPn ρ τ)) (ρ.prod (psiN τ))

def PhiGP : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (m j : ℕ) (ρ : GRep k m) (τ : MRep k (j + 1)), IsSmooth ρ.ρ → IsSmooth τ.ρ →
      MIso (phiN ψ (mcast (by omega : m + (j + 1) = (m + j) + 1) (prodGPn ρ τ))) (prodGPn ρ (phiN ψ τ))

def PsiPG : Prop :=
  ∀ (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ)

def PhiPG : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)), IsSmooth τ.ρ → IsSmooth σ.ρ →
      MExt (mcast (by omega) (prodPGn (phiN ψ τ) σ))
        (phiN ψ (mcast (by omega : (i + 1) + (t + 1) = (i + t + 1) + 1) (prodPGn τ σ)))
        (mcast (by omega) (prodGPn (psiN τ) (gres σ)))

def LeibnizOrd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (r t ℓ n : ℕ) (hn : r + t = n + ℓ) (π₁ : GRep k r) (π₂ : GRep k t), IsSmooth π₁.ρ → IsSmooth π₂.ρ →
      ∃ F : ℕ → Subrepresentation (derivB ψ ℓ ((π₁.prod π₂).cast hn)).ρ,
        Antitone F ∧ F 0 = ⊤ ∧ F (ℓ + 1) = ⊥ ∧
        ∀ i ≤ ℓ,
          if h : i ≤ r ∧ ℓ - i ≤ t then
            ∃ hsz : (r - i) + (t - (ℓ - i)) = n,
              Nonempty ((subQuot (F i) (F (i + 1))).Equiv
                ((((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).prod
                  ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2))).cast hsz).ρ)
          else F i = F (i + 1)

end GlobalTheory.RgGu.Leib

end
