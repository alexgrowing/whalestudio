import Mathlib

open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

abbrev NZIdeal (E : Type) [Field E] [NumberField E] : Type := {a : Ideal (𝓞 E) // a ≠ ⊥}

abbrev Prm (E : Type) [Field E] [NumberField E] : Type := IsDedekindDomain.HeightOneSpectrum (𝓞 E)

def Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : ℕ := Ideal.absNorm q.asIdeal

def Lser (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' a : NZIdeal E, χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

def Psum (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))

def abelian₂ (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, -Complex.log (1 - χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))

def PE (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-s)

def Pcl (E : Type) [Field E] [NumberField E] (l : ℕ) (a : ZMod l) (s : ℝ) : ℝ :=
  ∑' q : Prm E, if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0

end

end ReciprocityTheory.Cheb
