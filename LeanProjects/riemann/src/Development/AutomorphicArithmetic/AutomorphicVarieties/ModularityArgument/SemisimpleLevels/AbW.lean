import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne

namespace UpperTheory.V.Lev

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (X - 1) ^ x.lpDim

def Cmp (x y : WD h) : Prop := AbW x ∨ AbW y → x = y

theorem Cmp.of_eq {x y : WD h} (e : x = y) : Cmp x y := fun _ => e

theorem Cmp.left {x y : WD h} (c : Cmp x y) (a : AbW x) : x = y := c (Or.inl a)

theorem Cmp.right {x y : WD h} (c : Cmp x y) (a : AbW y) : x = y := c (Or.inr a)

end UpperTheory.V.Lev

end
