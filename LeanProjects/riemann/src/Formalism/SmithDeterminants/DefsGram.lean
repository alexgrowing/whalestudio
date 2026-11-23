import Formalism.SmithDeterminants.StatementGram

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.A

def RowDvdZ : Prop :=
  ∀ (σ ι : Type) (E : ι → MvPolynomial σ ℤ) (α : ι → (σ →₀ ℕ)) (a b : ι),
    (mfact (α a) : ℤ) ∣ gramZ (famZ E α) a b

def RowDvdG : Prop :=
  ∀ (σ ι : Type) (E : ι → MvPolynomial σ GaussianInt) (α : ι → (σ →₀ ℕ)) (a b : ι),
    (mfact (α a) : GaussianInt) ∣ gramG (famG E α) a b

def PosDefZ : Prop :=
  ∀ (σ ι : Type) [Fintype ι] (f : ι → MvPolynomial σ ℤ), LinearIndependent ℤ f →
    ((gramZ f).map (Int.cast : ℤ → ℝ)).PosDef

def PosDefG : Prop :=
  ∀ (σ ι : Type) [Fintype ι] (f : ι → MvPolynomial σ GaussianInt),
    LinearIndependent GaussianInt f → ((gramG f).map GaussianInt.toComplex).PosDef

def HadamardR : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosSemidef →
    A.det ≤ ∏ i, A i i

def HadamardC : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), A.PosSemidef →
    A.det ≤ ∏ i, A i i

def DiagZ : Prop :=
  ∀ (k s : ℕ) (E : MvPolynomial (Fin k) ℤ) (e : ℕ) (α : Fin k →₀ ℕ),
    E.IsHomogeneous e → Finsupp.degree α + e = s → l1Z E ≤ (k : ℤ) ^ e →
    fockZ (E * MvPolynomial.monomial α 1) (E * MvPolynomial.monomial α 1) ≤
      (mfact α : ℤ) * ((k : ℤ) ^ 2 * s) ^ e

def DiagG : Prop :=
  ∀ (k s : ℕ) (E : MvPolynomial (Fin k) GaussianInt) (e : ℕ) (α : Fin k →₀ ℕ),
    E.IsHomogeneous e → Finsupp.degree α + e = s → l1G E ≤ (k : ℝ) ^ e →
    (fockG (E * MvPolynomial.monomial α 1) (E * MvPolynomial.monomial α 1)).im = 0 ∧
    (fockG (E * MvPolynomial.monomial α 1) (E * MvPolynomial.monomial α 1)).re ≤
      (mfact α : ℤ) * ((k : ℤ) ^ 2 * s) ^ e

def MfactDvd : Prop :=
  ∀ (σ : Type) (α : σ →₀ ℕ), mfact α ∣ (Finsupp.degree α).factorial

def DetIntG : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι GaussianInt), A.conjTranspose = A →
    ∃ N : ℤ, A.det = (N : GaussianInt)

def AssembleZ : Prop := RowDvdZ → PosDefZ → HadamardR → DiagZ → MfactDvd → GramZ

def AssembleG : Prop := RowDvdG → PosDefG → HadamardC → DiagG → DetIntG → GramGauss

end Formalism.A
