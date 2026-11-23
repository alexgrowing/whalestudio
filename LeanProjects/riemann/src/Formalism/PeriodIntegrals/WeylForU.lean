import Formalism.PeriodIntegrals.WeylForK
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

namespace PI

open PI.UpqRep Formalism.BasicNotions

def WeylForU : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b), (Λ a - Λ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
      ∏ i ∈ Finset.range N, (i.factorial : ℝ)

def NablaDim : Prop :=
  ∀ (n : ℕ) (nu : Fin n → ℕ), Antitone nu →
    (Module.finrank ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n nu) : ℚ) =
      ∏ i : Fin n, ∏ j : Fin n,
        if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

def ModelIso : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    ∃ lam : DomWeight N, (∀ a, Λ a = ((lam.w a : ℤ) : ℝ)) ∧
      Module.finrank ℂ S = Module.finrank ℂ (nablaSq ℂ N lam)

def PolyCoef : Prop :=
  ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → FiniteDimensional ℂ S → IsKStableOn (allPos N) σ S →
    ∀ v ∈ S, ∀ w : H, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ w (σ g v) * g.det ^ k = MvPolynomial.eval (fun ij => g ij.1 ij.2) P

end PI
