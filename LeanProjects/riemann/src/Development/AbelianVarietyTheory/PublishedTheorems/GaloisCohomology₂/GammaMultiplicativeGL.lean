import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def GammaMultiplicativeGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n m t : ℕ) (π : IrrRep (GL (Fin n) k)) (τ : IrrRep (GL (Fin m) k)) (ρ : Fin t → IrrGL k) (z : Fin t → ℝ)
      (hd : ∑ i, ((ρ i).nu (z i)).1 = m) (e : Fin t → ℂ), 0 < m → m < n →
      IsCuspidal π.ρ → GlobalTheory.Whittaker.IsGeneric ψ π.ρ → GlobalTheory.Whittaker.IsGeneric ψ⁻¹ τ.ρ →
      (∀ i, (ρ i).IsCusp ∧ IsUnitarisable (ρ i).rep) → Antitone z →
      IsSubquotient τ.ρ (prodIrr (fun i => (ρ i).nu (z i)) hd) →
      (∀ i, HasPairGamma ψ π.ρ ((ρ i).nu (z i)).rep (e i)) → HasPairGamma ψ π.ρ τ.ρ (∏ i, e i)

end GlobalTheory.Published

end
