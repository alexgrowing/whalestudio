import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.RepGApply

noncomputable section

open NumberField Polynomial
open scoped Matrix

namespace UpperTheory.V.Z.Sym.Wt

def MemMH : Prop :=
  ∀ (K : Type) [Fintype K] (d : ℕ) (n : K → ℕ) (P : MvPolynomial (K × Fin d) ℂ),
    P ∈ MH d n ↔ ∀ m ∈ P.support, ∀ k, ∑ i, m (k, i) = n k

def FinMH : Prop := ∀ (K : Type) [Fintype K] (d : ℕ) (n : K → ℕ), FiniteDimensional ℂ (MH d n)

def tr1 (d n : ℕ) (g : GL (Fin d) ℂ) : ℂ := LinearMap.trace ℂ _ (mRep d (fun _ : Unit => n) fun _ => g)

def TrOne : Prop :=
  ∀ (d n : ℕ) (g : GL (Fin d) ℂ) (α : Fin d → ℂ), (g : Matrix (Fin d) (Fin d) ℂ).charpoly = ∏ i, (X - C (α i)) →
    tr1 d n g = MvPolynomial.eval α (MvPolynomial.hsymm (Fin d) ℂ n)

def TrProd : Prop :=
  ∀ (K : Type) [Fintype K] (d : ℕ) (n : K → ℕ) (g : K → GL (Fin d) ℂ),
    LinearMap.trace ℂ _ (mRep d n g) = ∏ k, tr1 d (n k) (g k)

def TrSwap : Prop :=
  ∀ (I : Type) [Fintype I] (d : ℕ) (n : I → ℕ) (g : I → GL (Fin d) ℂ),
    LinearMap.trace ℂ _ (biRep d n g * swp d n) = ∏ v, tr1 d (n v) (g v * invT ℂ d (g v))

def HqTwo : Prop := ∀ (j : ℕ) (a b : ℂ), MvPolynomial.eval ![a, b] (MvPolynomial.hsymm (Fin 2) ℂ j) = hq (a + b) (a * b) j

def HqThree : Prop :=
  ∀ (j : ℕ) (a b : ℂ), MvPolynomial.eval ![a, 1, b] (MvPolynomial.hsymm (Fin 3) ℂ (j + 1)) -
    MvPolynomial.eval ![a, 1, b] (MvPolynomial.hsymm (Fin 3) ℂ j) = hq (a + b) (a * b) (j + 1)

def HqKappa : Prop := ∀ (j : ℕ) (τ : ℂ), hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j

def ThFacts : Prop :=
  ∀ (I : Type) [Fintype I] (j : ℕ), thG I j * thG I j = 1 ∧
    ∀ g : I → GL (Fin 3) ℂ, thG I j * repG I j g = repG I j (fun v => invT ℂ 3 (g v)) * thG I j

def TwineC : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (j : ℕ), 1 ≤ j → ∀ (g : I → GL (Fin 3) ℂ) (τ : I → ℂ),
    (∀ v, ((g v * invT ℂ 3 (g v) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).charpoly = (X - 1) * (X ^ 2 - C (τ v) * X + 1)) →
    LinearMap.trace ℂ _ (repG I j g * thG I j) = ∏ v, hq (τ v) 1 j

def TrDC : Prop :=
  ∀ (I : Type) [Fintype I] (n : ℕ) (e : ℤ) (g : I → GL (Fin 2) ℂ),
    LinearMap.trace ℂ _ (repD I n e g) = ∏ v, ((g v : Matrix (Fin 2) (Fin 2) ℂ).det ^ e *
      hq (g v : Matrix (Fin 2) (Fin 2) ℂ).trace (g v : Matrix (Fin 2) (Fin 2) ℂ).det n)

def Scalars : Prop :=
  ∀ (I : Type) [Fintype I] (s : I → ℂˣ),
    (∀ j, repG I j (fun v => Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) = 1) ∧
    ∀ (n : ℕ) (e : ℤ), repD I n e (fun v => Matrix.GeneralLinearGroup.scalar (Fin 2) (s v)) =
      ((∏ v, s v ^ ((n : ℤ) + 2 * e) : ℂˣ) : ℂ) • (1 : Module.End ℂ (VD I n))

def ContRep : Prop :=
  ∀ (I : Type) [Fintype I],
    (∀ j (x : VG I j) (f : VG I j →ₗ[ℂ] ℂ), Continuous fun g => f (repG I j g x)) ∧
    ∀ n e (x : VD I n) (f : VD I n →ₗ[ℂ] ℂ), Continuous fun g => f (repD I n e g x)

structure Out {R I : Type} [CommRing R] [Fintype I] (em : I → R →+* ℂ) (j : ℕ) : Prop where
  finG : FiniteDimensional ℂ (VG I j)
  finD : ∀ n, FiniteDimensional ℂ (VD I n)
  th_sq : thG I j * thG I j = 1
  th_rep : ∀ g, thG I j * WG em j g = WG em j (invT R 3 g) * thG I j
  scalG : ∀ x : Rˣ, WG em j (Matrix.GeneralLinearGroup.scalar (Fin 3) x) = 1
  scalD : ∀ (n : ℕ) (e : ℤ) (x : Rˣ), WD em n e (Matrix.GeneralLinearGroup.scalar (Fin 2) x) =
    (∏ w, em w (x : R) ^ ((n : ℤ) + 2 * e)) • (1 : Module.End ℂ (VD I n))
  twine : ∀ (δ : GL (Fin 3) R) (τ : R),
    ((δ * invT R 3 δ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).charpoly = (X - 1) * (X ^ 2 - C τ * X + 1) →
    LinearMap.trace ℂ _ (WG em j δ * thG I j) = chi em j τ
  stable : ∀ (e : ℤ) (γ : GL (Fin 2) R), (γ : Matrix (Fin 2) (Fin 2) R).det = 1 →
    LinearMap.trace ℂ _ (WD em j e γ) = chi em j (γ : Matrix (Fin 2) (Fin 2) R).trace
  kappa : ∀ (z : GL (Fin 2) R) (τ : R), (z : Matrix (Fin 2) (Fin 2) R).trace = 2 + τ → (z : Matrix (Fin 2) (Fin 2) R).det = 2 + τ →
    LinearMap.trace ℂ _ (WD em (2 * j + 1) (-((j : ℤ) + 1)) z) = chi em j τ

def WtMain : Prop := ∀ (R I : Type) [CommRing R] [Fintype I] (em : I → R →+* ℂ) (j : ℕ), 1 ≤ j → Out em j

end UpperTheory.V.Z.Sym.Wt

end
