import Formalism.LocalToGlobal.InertKernelTheory.DefsMMIsom

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def LocBasisMM : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∃ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b ∧
      ‖(Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E))).det‖ = 1 ∧
      (Matrix.of fun (τ τ' : D.what₂.Tau) =>
        lamC lam (embT D τ (b (Fintype.equivFin D.what₂.Tau τ') 0 0))).det ≠ 0

def RatCoord : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
        (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
      ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) →
      Formalism.L2.Th1.H.relIdx
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
        (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ∀ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b →
    ∃ c : Fin 4 × D.what₂.Tau → Fin 4 → Fin (Fintype.card D.what₂.Tau) → D.host.K,
      (∀ w i' τ, g₁.symm (Pi.single w 1) (i', τ) =
        ∑ m, D.host.φ₀ ((c w i' m : D.host.K) : D.host.E) * embT D τ (b m 0 0)) ∧
      (∀ w i' m, ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : D.host.K) * c w i' m)) ∧
      ∀ w w', ∑ i', ∑ m, ∑ n, ((c w i' m : D.host.K) : D.host.E) * ((hYY D (b m) (b n) : D.host.K) : D.host.E) *
        D.host.conj ((c w' i' n : D.host.K) : D.host.E) = if w = w' then 1 else 0

def FixConj : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ → ∀ y : MaximalUnramifiedExtension p, σ (σ y) = y →
      (y : ℂ_[p]) ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) ∧
      ∀ σp : ℂ_[p] →+* ℂ_[p], IsConjP D lam σp → σp (y : ℂ_[p]) = ((σ y : MaximalUnramifiedExtension p) : ℂ_[p])

end Formalism.L2.KerInert
