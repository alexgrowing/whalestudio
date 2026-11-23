import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Short

open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0

variable (F : Type) [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] (D : ℕ) {N : ℕ}

abbrev coefField (x : Fin N → Ω) : IntermediateField F (OmS Ω D N) :=
  IntermediateField.adjoin F (Set.range (sImg (D := D) (0 : Fin (N + 1)) x))

def secDeg (x : Fin N → Ω) : ℕ := Module.finrank (coefField F D x) (OmS Ω D N)

def genForm (x : Fin N → Ω) : OmS Ω D N :=
  ∑ j : Fin (N + 1), sImg (D := D) (0 : Fin (N + 1)) x (0, j) * algebraMap Ω (OmS Ω D N) (Fin.cons (α := fun _ => Ω) 1 x j)

def normForm (x : Fin N → Ω) : OmS Ω D N := (Algebra.norm (coefField F D x) (genForm D x) : coefField F D x)

variable {F D} in

def InS (g : MvPolynomial (TVar D N) F) : Prop := ∀ p ∈ g.vars, p.1 ≠ 0

def IsNormChow (x : Fin N → Ω) (Ch : MvPolynomial (TVar D N) F) : Prop :=
  (∃ a b : MvPolynomial (TVar D N) F, a ≠ 0 ∧ b ≠ 0 ∧ InS a ∧ InS b ∧
    sHom (0 : Fin (N + 1)) x Ch * sHom (0 : Fin (N + 1)) x b = sHom (0 : Fin (N + 1)) x a * normForm F D x) ∧
  ∀ g, InS g → g ∣ Ch → IsUnit g

variable {F D} in

def IsGroupHomog (δ : ℕ) (G : MvPolynomial (TVar D N) F) : Prop :=
  ∀ i : Fin (D + 1), G.IsWeightedHomogeneous (fun p : TVar D N => if p.1 = i then 1 else 0) δ

example (c : F) : InS (C c : MvPolynomial (TVar D N) F) := fun p hp => by simp [vars_C] at hp

end GlobalTheory.CompanionTheory.Ar.Short
