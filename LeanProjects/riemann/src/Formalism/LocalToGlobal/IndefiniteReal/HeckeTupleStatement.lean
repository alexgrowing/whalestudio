import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

namespace Formalism.IndefR.HeckeTupleConditions

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef

noncomputable def Atup {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (S : IndefData Df) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (S.Iw j t w : ℝ) + (S.Iw j t (conjPl w) : ℝ) + (jw (Df.HT j t) w (Df.Tl j t) : ℝ)

def UntwistedOfSupportAtTwistedPlaces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (S : IndefData Df) (N : IndefNum Bs),
    (∀ w : HeightOneSpectrum (𝓞 K), (∃ j, Atup S j Bs.μ0 w ≠ 0 ∨ N.F0 w j ≠ 0) → S.μ w ≠ Bs.μ0) →
    (∀ w, w ∈ S.Tw ↔ S.μ w ≠ Bs.μ0) →
    S.Untwisted N

end Formalism.IndefR.HeckeTupleConditions
