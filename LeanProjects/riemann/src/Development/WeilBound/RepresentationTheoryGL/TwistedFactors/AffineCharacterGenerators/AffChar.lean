import Mathlib

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Fx

abbrev EP (ι : Type) : Type := AddMonoidAlgebra (MvPolynomial ι ℂ) (ι → ℝ)

abbrev KF (ι κ : Type) : Type := MvPolynomial κ (EP ι)

variable {ι ι' κ : Type}

def l1 (p : MvPolynomial ι ℂ) : ℝ := ∑ α ∈ p.support, ‖p.coeff α‖

def lin [Fintype ι] (v : ι → ℝ) : MvPolynomial ι ℂ := ∑ i, C (v i : ℂ) * X i

def lift {A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) : EP ι →+* A :=
  AddMonoidAlgebra.liftNCRingHom (aeval x).toRingHom τ fun _ _ => Commute.all _ _

def expChar [Fintype ι] (Λ : ι → ℂ) : Multiplicative (ι → ℝ) →* ℂ where
  toFun v := Complex.exp (∑ i, (v.toAdd i : ℂ) * Λ i)
  map_one' := by simp
  map_mul' v w := by simp [add_mul, Finset.sum_add_distrib, Complex.exp_add]

def ev [Fintype ι] (Λ : ι → ℂ) : EP ι →+* ℂ := lift Λ (expChar Λ)

def evK [Fintype ι] (Λ : ι → ℂ) (h : κ → ℂ) : KF ι κ →+* ℂ := eval₂Hom (ev Λ) h

def piece [Fintype ι] (k : ℕ) (f : EP ι) : MvPolynomial ι ℂ :=
  f.coeff.sum fun v p => ∑ b ∈ Finset.range (k + 1),
    homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b)

def pieceK [Fintype ι] (k : ℕ) (F : KF ι κ) : MvPolynomial κ (MvPolynomial ι ℂ) :=
  ∑ β ∈ F.support, monomial β (piece k (F.coeff β))

def affChar [Fintype ι] (Λ₀ : ι → ℂ) (M : Matrix ι ι' ℝ) : Multiplicative (ι → ℝ) →* EP ι' where
  toFun v := AddMonoidAlgebra.single (Matrix.vecMul v.toAdd M) (C (expChar Λ₀ v))
  map_one' := by simp [AddMonoidAlgebra.one_def]
  map_mul' v w := by simp [AddMonoidAlgebra.single_mul_single, Matrix.add_vecMul]

def aff [Fintype ι] [Fintype ι'] (Λ₀ : ι → ℂ) (M : Matrix ι ι' ℝ) : EP ι →+* EP ι' :=
  lift (fun i => AddMonoidAlgebra.single 0 (C (Λ₀ i) + lin (M i))) (affChar Λ₀ M)

def ren [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') : EP ι →+* EP ι' :=
  aff 0 (Matrix.of fun i j => if δ i = j then 1 else 0)

structure Fam (ι κ : Type) [Fintype ι] where
  r : ℕ
  Λ : ι → ℂ
  emb : Matrix ι (Fin r) ℝ
  pr : Matrix (Fin r) ι ℝ
  pr_emb : pr * emb = 1
  h : κ → EP (Fin r)

def Fam.sub [Fintype ι] (b : Fam ι κ) : KF ι κ →+* EP (Fin b.r) := eval₂Hom (aff b.Λ b.emb) b.h

def Fam.Mem [Fintype ι] (b : Fam ι κ) (Λ : ι → ℂ) (h : κ → ℂ) : Prop :=
  ∃ lam : Fin b.r → ℂ, (∀ i, Λ i = b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) ∧ ∀ k, h k = ev lam (b.h k)

def Fam.point [Fintype ι] (Λ : ι → ℂ) (h : κ → ℂ) : Fam ι κ where
  r := 0
  Λ := Λ
  emb := 0
  pr := 0
  pr_emb := Subsingleton.elim _ _
  h k := AddMonoidAlgebra.single 0 (C (h k))

def blockE {τ : Type} {n : ℕ} (ti : τ × Fin n) : MvPolynomial (τ × Fin n) ℂ :=
  rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))

def cheb (η : ℝ) (m : ℕ) (a : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ m).eval (2 * a / η - 1)

end PositivityTheory.Rg.Fx
