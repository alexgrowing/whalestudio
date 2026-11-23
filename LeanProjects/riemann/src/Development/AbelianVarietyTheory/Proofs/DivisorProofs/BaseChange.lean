import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWt

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def JointWt (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) : Prop :=
  ∃ z : Gm, z ≠ 0 ∧ ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z = z

def pot {ι : Type} [Fintype ι] (w : ι → Fin N → ℕ) : ℕ := ∑ τ, ∑ a : Fin N, (N - (a : ℕ)) * w τ a

def extW {ι : Type} (w : ι → Fin N → ℕ) : ι → ℕ → ℕ := fun τ a => if h : a < N then w τ ⟨a, h⟩ else 0

def genSub (f : MvPolynomial (Fin N × Fin N) O) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2))) f

def IsCoef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (a : Module.End O (NablaT O N lam)) : Prop :=
  ∀ (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) = (genSub O N (x τ : MvPolynomial (Fin N × Fin N) O)).coeff m →
    a (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)

def CoefIn : Prop := ∀ (τ : ι) (m : Fin N × Fin N →₀ ℕ), ∃ a : alg O N lam, IsCoef O N lam τ m a

def BaseChange : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    (∀ f ∈ dualWeyl (O ⧸ Ideal.span {ϖ}) N N ν, ∃ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f) ∧
    (∀ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = 0 → ∃ h ∈ dualWeyl O N N ν, g = ϖ • h)

theorem res_extW {ι : Type} (w : ι → Fin N → ℕ) (τ : ι) : res N (extW N w τ) = w τ := by
  funext a
  simp [res, extW, a.isLt]

end GlobalTheory.HighWt

end
