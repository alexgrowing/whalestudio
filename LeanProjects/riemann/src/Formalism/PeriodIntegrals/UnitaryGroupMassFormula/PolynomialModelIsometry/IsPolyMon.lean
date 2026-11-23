import Formalism.PeriodIntegrals.WeylForU
import Formalism.PeriodIntegrals.UnitaryDense
import Formalism.PeriodIntegrals.HwIrred
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

def evM {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  eval (fun ij => g ij.1 ij.2) Q

def detPoly (N : ℕ) : MvPolynomial (Fin N × Fin N) ℂ :=
  (Matrix.of fun i j : Fin N => (X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det

def torus {N : ℕ} (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

structure IsPolyMon {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)) : Prop where
  mul : ∀ g h, P (g * h) = P g ∘ₗ P h
  one : P 1 = LinearMap.id
  poly : ∀ x y : V, ∃ Q : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q = ⟪y, P g x⟫_ℂ

def PolyExt : Prop :=
  ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → FiniteDimensional ℂ S → IsKStableOn (allPos N) σ S →
    ∃ (K : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S)), IsPolyMon P ∧
      ∀ g ∈ Kset (allPos N), ∀ x : S, ((P g x : S) : H) = g.det ^ K • σ g (x : H)

def LamInt : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v : H),
    IsURepOn (Kset (allPos N)) σ → v ≠ 0 → IsWtOn (Kset (allPos N)) σ Λ v →
    ∀ a, ∃ m : ℤ, Λ a = m

def TorusEig : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (K : ℕ)
    (P : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S)),
    IsURepOn (Kset (allPos N)) σ → IsKStableOn (allPos N) σ S →
    (∀ g ∈ Kset (allPos N), ∀ x : S, ((P g x : S) : H) = g.det ^ K • σ g (x : H)) →
    ∀ v0 : S, IsWtOn (Kset (allPos N)) σ Λ (v0 : H) →
    ∀ (θ : Fin N → ℝ) (x : S),
      ⟪v0, P (torus θ) x⟫_ℂ = Complex.exp (((∑ a, (Λ a + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ

def LowerInv : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (K : ℕ)
    (P : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S)),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S → IsPolyMon P →
    (∀ g ∈ Kset (allPos N), ∀ x : S, ((P g x : S) : H) = g.det ^ K • σ g (x : H)) →
    ∀ v0 : S, IsWtOn (Kset (allPos N)) σ Λ (v0 : H) →
    ∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : S),
      ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ

def ModelMap : Prop :=
  ∀ (N : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)) (v0 : V) (μ : Fin N → ℤ) (K : ℕ),
    IsPolyMon P → v0 ≠ 0 →
    (∀ (θ : Fin N → ℝ) (x : V), ⟪v0, P (torus θ) x⟫_ℂ =
      Complex.exp (((∑ a, ((μ a : ℝ) + K) * θ a : ℝ) : ℂ) * Complex.I) * ⟪v0, x⟫_ℂ) →
    (∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : V), ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ) →
    ∃ (ν : Fin N → ℕ) (F : V →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      (∀ a, (ν a : ℤ) = μ a + K) ∧ (∀ x, F x ∈ dualWeyl ℂ N N ν) ∧ F v0 ≠ 0 ∧
      ∀ g x, F (P g x) = rowAct ℂ (n := N) gᵀ (F x)

def DetSplit : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (c : ℕ), (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0) →
    ∀ f ∈ dualWeyl ℂ N N (fun a => ν a + c), ∃ f' ∈ dualWeyl ℂ N N ν, f = detPoly N ^ c * f'

end PI.WMI
