import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
