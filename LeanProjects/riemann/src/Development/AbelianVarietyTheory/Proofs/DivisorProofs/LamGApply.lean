import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

def detPol (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.det (Matrix.of fun a s => X (a, s))

def liftPol {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (Fin n × Fin n) C :=
  detPol C n ^ k * MvPolynomial.map e0 f

def Shift {ι : Type} {n : ℕ} (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) : Prop :=
  ∀ τ (a : Fin n), (lamW τ a : ℤ) = (lam τ).w a + c τ

def IsPhi {K C : Type} [Field K] [Field C] {ι : Type} [Fintype ι] {n : ℕ} (e0 : K →+* C) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ)
    (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW) : Prop :=
  ∀ (x : ι → MvPolynomial (Fin n × Fin n) K) (v : VV K lam), (∀ τ, x τ ∈ nablaSq K n (lam τ)) → (v : Pol K ι n) = ten x →
    ∃ y : ∀ τ, dualWeyl C n n (res n (lamW τ)),
      (∀ τ, (y τ : MvPolynomial (Fin n × Fin n) C) = liftPol e0 (lamW τ (n - 1)) (x τ)) ∧ Φ v = PiTensorProduct.tprod C y

def lamG (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) :
    (ι → GL (Fin n) C) →* Module.End C (NablaT C n lamW) where
  toFun g := ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g
  map_one' := by simp [grp]
  map_mul' g h := by
    simp only [grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

theorem lamG_apply (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ)
    (g : ι → GL (Fin n) C) (z : NablaT C n lamW) :
    lamG C n lamW c g z = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g z := rfl

def AtPlace {K : Type} [Field K] [NumberField K] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) : Prop :=
  ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1

end GlobalTheory.FrameRead
