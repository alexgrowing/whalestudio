import Formalism.SatakeDualWeyl.Statement
import Formalism.GradedWeylDivisibility.StatementA

noncomputable section

open MvPolynomial

namespace Formalism.UG

def dwAct (R : Type) [CommRing R] (r n : ℕ) (g : GL (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  Formalism.GradedWeylDivisibility.rowAct R (n := n) ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)

def oneCol (R : Type) [CommRing R] (r : ℕ) :
    MvPolynomial (Fin r × Fin 1) R →ₐ[R] MvPolynomial (Fin r) R :=
  rename (Prod.fst : Fin r × Fin 1 → Fin r)

def DwActMul : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (g h : GL (Fin r) R),
    dwAct R r n (g * h) = (dwAct R r n g).comp (dwAct R r n h) ∧ dwAct R r n 1 = AlgHom.id R _

def DwStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν

def WeylGLStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

def WeylGLStableLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

def OneColAct : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (g : GL (Fin r) R) (f : MvPolynomial (Fin r × Fin 1) R),
    oneCol R r (dwAct R r 1 g f) = polyAct R (Fin r) g (oneCol R r f)

def DualWeylOne : Prop :=
  ∀ (R : Type) [CommRing R] (r k : ℕ),
    (Formalism.GradedWeylDivisibility.dualWeyl R r 1 (fun _ => k)).map (oneCol R r).toLinearMap = nabla R (Fin r) k

def WeylOne : Prop :=
  ∀ (R : Type) [CommRing R] (r k : ℕ) (hr : 1 ≤ r),
    (Formalism.GradedWeylDivisibility.weyl R r 1 hr (fun _ => k)).map (oneCol R r).toLinearMap = weylSub R (Fin r) k

def OneColInj : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), Function.Injective (oneCol R r)

end Formalism.UG
