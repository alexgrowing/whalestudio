import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mHom (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℕ) : Submodule ℤ (MRing ι) :=
  Submodule.span ℤ {s | IsMultiHomog s a}

def mPiece (W : Ideal (MRing ι)) (a : K → ℕ) : Submodule ℤ (MRing ι ⧸ W) :=
  (mHom ι a).map (Ideal.Quotient.mkₐ ℤ W).toLinearMap

end

abbrev FinTwoTypeFamily (κ : Type) : Fin 2 → Type := fun _ => κ

variable {Ω : Type} [Field Ω] {κ : Type}

def pair (x x' : Ix κ → Ω) : (Σ k, FinTwoTypeFamily κ k) → Ω :=
  fun p => if p.1 = 0 then x ⟨(), p.2⟩ else x' ⟨(), p.2⟩

def latIndex [CharZero Ω] (x x' : Ix κ → Ω) (n : ℕ) : ℕ :=
  (sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
