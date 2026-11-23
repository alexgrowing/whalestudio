import Mathlib

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain

def vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk la.asIdeal).count (Associates.mk I).factors

def discAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] : Ideal (𝓞 K) :=
  Ideal.span {(((discr E).natAbs : ℕ) : 𝓞 K)}

def mOf (E : Type) [Field E] [NumberField E] {K : Type} [Field K] [NumberField K] (n' : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  max (vla la (discAt E K)) (vla la (Ideal.span {(n' : 𝓞 K)}))

def beOf (E : Type) [Field E] [NumberField E] {K : Type} [Field K] [NumberField K] (n' A : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (A : ℝ) * (mOf E n' la : ℝ)

def lrdOf (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (|((NumberField.discr E : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))

def BeSumStatement : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (n' A : ℕ), 0 < n' →
    (Function.support (beOf E (K := K) n' A)).Finite ∧
    (∑ᶠ la, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ)) / (Module.finrank ℚ K : ℝ) ≤
      (Real.log |((discr E : ℤ) : ℝ)| + Real.log n') * A

end Formalism.L2.Pj.QAt
