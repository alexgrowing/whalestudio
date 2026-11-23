import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial UpperTheory.V.Af

namespace UpperTheory.V.Published

def RepNewform : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ f.M → ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Published
