import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix MvPolynomial
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCompose

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Vr (N : ℕ) : Type := (Fin N × Fin N) ⊕ (Fin N × Fin N)

def vars {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) : Vr N → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

def lin {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : Vr N → MvPolynomial (Vr N) ℂ
  | Sum.inl x => ∑ c : Fin N, C (X c x.2) * MvPolynomial.X (Sum.inl (x.1, c))
  | Sum.inr x => ∑ c : Fin N, C (star (X c x.2)) * MvPolynomial.X (Sum.inr (x.1, c))

def dP {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Vr N) ℂ) : MvPolynomial (Vr N) ℂ :=
  ∑ i : Vr N, pderiv i q * lin X i

def zP (k j ρ : ℕ) : Matrix (Fin j) (Fin j) (MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

def zPb (k j ρ : ℕ) : Matrix (Fin j) (Fin j) (MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inr (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

def qD (k j ρ : ℕ) : MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ := (zP k j ρ).det

def qDb (k j ρ : ℕ) : MvPolynomial (Vr (2 * (j + ρ) + k + 1)) ℂ := (zPb k j ρ).det

abbrev SC (N : ℕ) : Type := MvPolynomial (Vr N) ℂ × ℕ × ℕ

def sv (k j ρ : ℕ) (s : SC (2 * (j + ρ) + k + 1)) (g : Mat k (j + ρ)) : ℂ :=
  eval (vars g) s.1 * (DjU k j ρ g)⁻¹ ^ s.2.1 * (star (DjU k j ρ g))⁻¹ ^ s.2.2

def mulSC {N : ℕ} (s t : SC N) : SC N := (s.1 * t.1, s.2.1 + t.2.1, s.2.2 + t.2.2)

abbrev FS (k r : ℕ) : Type := List (SC (2 * r + k + 1) × List (Mat k r))

section shape

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def shape (k j ρ : ℕ) (F : Mat k (j + ρ) → E) (L : FS k (j + ρ)) (g : Mat k (j + ρ)) : E :=
  (L.map fun e => sv k j ρ e.1 g • Rw e.2 F g).sum

end shape

def stepOne (k j ρ : ℕ) (X : Mat k (j + ρ)) (e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))) :
    FS k (j + ρ) :=
  [((dP X e.1.1, e.1.2.1, e.1.2.2), e.2),
   ((C (-(e.1.2.1 : ℂ)) * e.1.1 * dP X (qD k j ρ), e.1.2.1 + 1, e.1.2.2), e.2),
   ((C (-(e.1.2.2 : ℂ)) * e.1.1 * dP X (qDb k j ρ), e.1.2.1, e.1.2.2 + 1), e.2),
   (e.1, X :: e.2)]

def step (k j ρ : ℕ) (X : Mat k (j + ρ)) (L : FS k (j + ρ)) : FS k (j + ρ) := L.flatMap (stepOne k j ρ X)

def steps (k j ρ : ℕ) (w : List (Mat k (j + ρ))) (L : FS k (j + ρ)) : FS k (j + ρ) := w.foldr (step k j ρ) L

end PI.UnitaryGroupMassFormula.UsCompose
