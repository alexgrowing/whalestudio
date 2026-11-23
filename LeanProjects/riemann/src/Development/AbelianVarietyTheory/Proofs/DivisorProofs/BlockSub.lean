import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWtEmb

abbrev BVar (N : ℕ) (ι : Type) : Type := ι × (Fin N × Fin N)

abbrev OVar (N : ℕ) {ι : Type} (τ : ι) : Type := {p : BVar N ι // p.1 ≠ τ}

def blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  aeval fun v => X (τ, v)

def redT (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) :
    NablaT O N mu →ₗ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra O ι (MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}))).compLinearMap
    fun τ => (blockRed O N ϖ τ).toLinearMap ∘ₗ (dualWeyl O N N (res N (mu τ))).subtype)

def nabK (k : Type) [CommRing k] (N : ℕ) {ι : Type} [Fintype ι] (ν : ι → Fin N → ℕ) : Submodule k (MvPolynomial (BVar N ι) k) :=
  Submodule.span k {P | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ τ, f τ ∈ dualWeyl k N N (ν τ)) ∧
    P = ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)}

def toBlock (k : Type) [CommRing k] (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (Fin N × Fin N) (MvPolynomial (OVar N τ) k) :=
  aeval fun p => if h : p.1 = τ then X p.2 else C (X ⟨p, h⟩)

def blockSub (k : Type) [CommRing k] (N : ℕ) {ι : Type} (A : ι → Matrix (Fin N) (Fin N) k) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (BVar N ι) k :=
  aeval fun p => ∑ b : Fin N, C (A p.1 p.2.1 b) * X (p.1, (b, p.2.2))

def blockW (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) : BVar N ι → (Fin N → ℕ) :=
  fun p => if p.1 = τ then Pi.single p.2.1 1 else 0

end GlobalTheory.HighWtEmb

end
