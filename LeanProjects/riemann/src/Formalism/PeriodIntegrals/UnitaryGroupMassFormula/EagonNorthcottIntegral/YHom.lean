import Mathlib
import Formalism.PeriodIntegrals.EagonNorthcottZ

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

def sgn {D : ℕ} (i : Fin D) (J : Finset (Fin D)) : ℤ := (-1) ^ (J.filter (· < i)).card

abbrev P (D : ℕ) : Type := MvPolynomial (Fin D ⊕ Fin D) ℤ

abbrev S (D : ℕ) : Type := MvPolynomial (Fin D) ℤ

abbrev W (D : ℕ) : Type := Finset (Fin D) → P D

def K {D : ℕ} (t : Fin D → P D) (ω : W D) : W D :=
  fun J => ∑ i ∈ Jᶜ, (sgn i J : P D) * t i * ω (insert i J)

def ct {D : ℕ} (i : Fin D) (ω : W D) : W D :=
  fun J => if i ∈ J then 0 else (sgn i J : P D) * ω (insert i J)

def xs {D : ℕ} : Fin D → P D := fun i => X (Sum.inl i)

def ys {D : ℕ} : Fin D → P D := fun i => X (Sum.inr i)

def YHom {D : ℕ} (a : ℕ) (f : P D) : Prop := ∀ m ∈ f.support, ∑ i, m (Sum.inr i) = a

def Gr {D : ℕ} (a j : ℕ) (ω : W D) : Prop := (∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)

def inx {D : ℕ} : S D →ₐ[ℤ] P D := rename Sum.inl

def mu {D : ℕ} : P D →ₐ[ℤ] S D := aeval (Sum.elim X X)

def Dop {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) : P D →ₗ[ℤ] P D :=
  (basisMonomials (Fin D ⊕ Fin D) ℤ).constr ℤ fun m =>
    if 0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0 then monomial (m - Finsupp.single (ι i) 1) (1 : ℤ) else 0

def hom {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (ω : W D) : W D :=
  fun J => if h : J.Nonempty then Dop ι (J.min' h) (ω (J.erase (J.min' h))) else 0

end PI.EagonNorthcottZ
