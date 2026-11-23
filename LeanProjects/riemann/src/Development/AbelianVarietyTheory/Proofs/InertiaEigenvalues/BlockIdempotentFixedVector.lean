import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoBlockEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelOfParabolicVector
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

abbrev T₀ : GL {i : Fin (a + b) // twoBlock (a + b) a i = 0} (ZMod g) ≃* GlobalTheory.GLq.Gn g a :=
  (glEquiv (ZMod g) (firstBlock a b).symm).symm

abbrev T₁ : GL {i : Fin (a + b) // twoBlock (a + b) a i = 1} (ZMod g) ≃* GlobalTheory.GLq.Gn g b :=
  (glEquiv (ZMod g) (secondBlock a b).symm).symm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}
  (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))

def fnl (l₀ : (τ₀ : Type) →ₗ[ℂ] ℂ) (l₁ : (τ₁ : Type) →ₗ[ℂ] ℂ) :
    ∀ c : Fin 2, (twoRep τ₀ τ₁ c : Type) →ₗ[ℂ] ℂ
  | 0 => l₀
  | 1 => l₁

def pair (x₀ : (τ₀ : Type)) (x₁ : (τ₁ : Type)) : ∀ c : Fin 2, (twoRep τ₀ τ₁ c : Type)
  | 0 => x₀
  | 1 => x₁

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

def phi (l₀ : (τ₀ : Type) →ₗ[ℂ] ℂ) (l₁ : (τ₁ : Type) →ₗ[ℂ] ℂ) :
    PiTensorProduct ℂ (fun c => (twoRep τ₀ τ₁ c : Type)) →ₗ[ℂ] V :=
  PiTensorProduct.lift (∑ g₀ : GlobalTheory.GLq.Gn g a, ∑ g₁ : GlobalTheory.GLq.Gn g b,
    ((MultilinearMap.mkPiAlgebra ℂ (Fin 2) ℂ).compLinearMap
      (fnl τ₀ τ₁ (l₀ ∘ₗ τ₀.ρ g₀⁻¹) (l₁ ∘ₗ τ₁.ρ g₁⁻¹))).smulRight (ρ (GlobalTheory.GLp.blk a b (a + b) g₀ g₁) w))

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

open GlobalTheory.GLp.ParLabel

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}
  (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))
  {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

end GlobalTheory.SerOSys.TwoMap

namespace GlobalTheory.SerOSys.TwoMap

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

variable (τ₀ : FDRep ℂ (GL (Fin a) (ZMod g))) (τ₁ : FDRep ℂ (GL (Fin b) (ZMod g)))
  {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V)

end GlobalTheory.SerOSys.TwoMap
