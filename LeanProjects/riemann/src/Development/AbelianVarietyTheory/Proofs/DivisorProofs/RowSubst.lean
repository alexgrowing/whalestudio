import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
