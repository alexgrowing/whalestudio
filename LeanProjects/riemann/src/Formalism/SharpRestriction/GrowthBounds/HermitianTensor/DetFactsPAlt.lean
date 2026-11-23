import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def genY (A : Type) [CommRing A] (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) :=
  Matrix.of fun i j => X (i, j)

def cofY (A : Type) [CommRing A] (r : ℕ) : MvPolynomial (Fin r × Fin r) A →ₐ[A] MvPolynomial (Fin r × Fin r) A :=
  aeval fun v => (genY A r).adjugate v.2.rev v.1

def TauP : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [CharZero O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (r N e : ℕ) (α : Fin r → ℕ), 1 ≤ r → Antitone α → (∀ i, α i ≤ N) → (∀ i, e ≤ α i) → (∃ i, α i = e) →
    ∃ τ : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K,
      (∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev), τ f' ∈ dualWeyl K r r (fun i => α i - e)) ∧
      (∀ f' ∈ intO O r (fun i => N - α i.rev), τ f' ∈ intO O r (fun i => α i - e)) ∧
      (∀ g ∈ intO O r (fun i => α i - e), ∃ f' ∈ intO O r (fun i => N - α i.rev), τ f' = g) ∧
      (∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f' ∈ dualWeyl K r r (fun i => N - α i.rev),
        rowAct K l.transpose (τ (rowAct K l f')) = l.det ^ (N - e) • τ f')

def SmithP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) ν, ∀ Q ∈ intO R.O (m + 1) ν, B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (ν j : ℤ)) ∧ (∀ b, ka b ≤ N0 (m + 1) * deF p (m + 1) (ν 0)) ∧
        (∀ b, x b ∈ intO R.O (m + 1) ν) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) ν) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0

def BilinP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ)
    (B : MvPolynomial (Fin r × Fin r) K →ₗ[K] MvPolynomial (Fin r × Fin r) K →ₗ[K] K),
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K,
      ∀ f f', L (blockEmb K true f * blockEmb K false f') = B f f'

def DetFactsP : Prop :=
  ∀ (A : Type) [CommRing A] (r e : ℕ),
    detY A r ^ e ∈ dualWeyl A r r (fun _ => e) ∧
    ∀ l : Matrix (Fin r) (Fin r) A, rowAct A l (detY A r) = C l.det * detY A r

def NumP : Prop :=
  ∀ (p a c r ell : ℕ), 2 ≤ p → 1 ≤ r → ell ≤ c → c ≤ 8 * a → N0 r * deF p r ell ≤ ⌈kappaOneExponent p a (r + 1)⌉₊

end Formalism.MainNotions.flipOneThree.Pf

end
