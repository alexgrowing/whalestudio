import Mathlib
import Formalism.RealPlaceAnalysis.StatementE

noncomputable section

open Matrix

namespace UpperTheory.V.Weyl

structure Pre (n : ℕ) where

  d : ℕ

  mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ
  poly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g, mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p

variable {n : ℕ}

def Pre.coef (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) : ℂ := Ξ.mat (Matrix.of x) i j

abbrev oneM (n : ℕ) : Fin n → Fin n → ℂ := Matrix.of.symm 1

def Pre.D (Ξ : Pre n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℂ (Ξ.coef i j) (oneM n) (Matrix.of.symm X)
  map_add' X Y := by ext i j; exact map_add (fderiv ℂ (Ξ.coef i j) (oneM n)) X Y
  map_smul' c X := by ext i j; exact map_smul (fderiv ℂ (Ξ.coef i j) (oneM n)) c X

def Pre.E (Ξ : Pre n) (a b : Fin n) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := Ξ.D (Matrix.single a b 1)

def Pre.HasWt (Ξ : Pre n) (ν : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, Formalism.REAL.qdet Ξ.E u = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def Pre.IsTop (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ) : Prop :=
  ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → Ξ.mat b *ᵥ v = (∏ k, b k k ^ ν k) • v

def Pre.std (n : ℕ) : Pre n where
  d := n
  mat := MonoidHom.id _
  poly i j := ⟨MvPolynomial.X (i, j), fun g => by simp⟩

instance : Inhabited (Pre n) := ⟨Pre.std n⟩

abbrev Pol (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) ℂ

def rtr (g : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n :=
  MvPolynomial.aeval fun ij => ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2)

def minor (k : Fin n) : Pol n :=
  (Matrix.of fun i j : Fin (k + 1) =>
    (MvPolynomial.X (Fin.castLE k.2 i, Fin.castLE k.2 j) : Pol n)).det

end UpperTheory.V.Weyl
