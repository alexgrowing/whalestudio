import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.LocalRingCardinality.DataTheta

noncomputable section

open MvPolynomial Formalism.BasicNotions

namespace UpperTheory.TP.RP

abbrev PP (n d : ℕ) : Type := Formalism.BasicNotions.TH.Pol n 0 d 0

def xv {n d : ℕ} (i : Fin n) (j : Fin d) : PP n d := X (Sum.inl i, Sum.inl j)

def leftSub {n d : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : PP n d →ₐ[ℂ] PP n d :=
  aeval fun l => match l with
    | (Sum.inl b, Sum.inl c) => ∑ a, C (g a b) * xv a c
    | l => X l

def rightSub {n d : ℕ} (h : Matrix (Fin d) (Fin d) ℂ) : PP n d →ₐ[ℂ] PP n d :=
  aeval fun l => match l with
    | (Sum.inl b, Sum.inl c) => ∑ a, C (h a c) * xv b a
    | l => X l

def act1 {n d : ℕ} (c : ℤ) (g : GL (Fin n) ℂ) : Module.End ℂ (PP n d) :=
  detPow ℂ n g c • (leftSub g.1).toLinearMap

def act2 {n d : ℕ} (c : ℤ) (h : GL (Fin d) ℂ) : Module.End ℂ (PP n d) :=
  detPow ℂ d h c • (rightSub h.1).toLinearMap

def ofTall {n d : ℕ} : MvPolynomial (Fin d × Fin n) ℂ →ₐ[ℂ] PP n d := rename fun v => (Sum.inl v.2, Sum.inl v.1)

def joint {n d : ℕ} (h : n ≤ d) (μ : Fin n → ℕ) : PP n d := ofTall (Formalism.GradedWeylDivisibility.hw ℂ h μ)

end UpperTheory.TP.RP

end
