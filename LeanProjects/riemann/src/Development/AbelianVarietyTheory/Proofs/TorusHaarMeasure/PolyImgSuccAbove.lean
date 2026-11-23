import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

namespace GlobalTheory.GenericSection

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def polyImg (j0 : Fin (N + 1)) (x : Fin N → F) (p : TVar D N) :
    MvPolynomial (SVar D N) F :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) F) j0
    (if p.1 = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (p.1, k)) * C (x k))
    (fun k => X (Sum.inr (p.1, k))) p.2

def freeVar (j0 : Fin (N + 1)) : SVar D N → TVar D N :=
  Sum.elim (fun _ => (0, j0)) (fun q => (q.1, j0.succAbove q.2))

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_same (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0) =
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

open NumberField MvPolynomial in
variable {F : Type} [Field F] {D N : ℕ} in
theorem _root_.GlobalTheory.GenericSection.polyImg_succAbove (j0 : Fin (N + 1)) (x : Fin N → F)
    (i : Fin (D + 1)) (k : Fin N) :
    _root_.GlobalTheory.GenericSection.polyImg j0 x (i, j0.succAbove k) = X (Sum.inr (i, k)) := by
  simp [_root_.GlobalTheory.GenericSection.polyImg]

end GlobalTheory.GenericSection
