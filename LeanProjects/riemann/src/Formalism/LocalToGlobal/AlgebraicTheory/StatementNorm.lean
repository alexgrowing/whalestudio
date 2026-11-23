import Formalism.LocalToGlobal.AlgebraicTheory.StatementC

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual IsLat IsHerm IsPosDef Th alphaQ inter relIdx)
open Formalism.L2.Th1.GD (LocNorm)

def hPow {n : Type} (I : Type) [DecidableEq I] (h : Matrix n n ℂ) : Matrix (n × I) (n × I) ℂ :=
  fun w w' => if w.2 = w'.2 then h w.1 w'.1 else 0

def latPow {n : Type} (I : Type) (Λ : AddSubgroup (n → ℂ)) : AddSubgroup (n × I → ℂ) where
  carrier := {z | ∀ i, (fun k => z (k, i)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy i => Λ.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => Λ.neg_mem (hx i)

def fnPow {n : Type} (I : Type) [Fintype I] (θ : (n → ℂ) → ℂ) (z : n × I → ℂ) : ℂ := ∏ i, θ fun k => z (k, i)

def LocNormScale : Prop :=
  ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (c : ℂ), ‖ι c‖ ≤ 1 →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ (c • θ) p ι

def LocNormPow : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (I : Type) [Fintype I] [DecidableEq I],
    LocNorm a₀ b₀ dK ha hdK lam hlam (hPow I h) (latPow I Λ) (fnPow I θ) p ι

def LocNormInter : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ₁ Λ₂ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ₁ → IsLat Λ₂ →
    IsSelfDual (matH h) Λ₁ → IsSelfDual (matH h) Λ₂ →
    (∀ x ∈ Λ₁, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₁) → (∀ x ∈ Λ₂, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₂) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ¬ p ∣ relIdx Λ₁ Λ₂ →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₁ θ p ι →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₂ (inter (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁ Λ₂ θ) p ι

end Formalism.L2.AlgTh
