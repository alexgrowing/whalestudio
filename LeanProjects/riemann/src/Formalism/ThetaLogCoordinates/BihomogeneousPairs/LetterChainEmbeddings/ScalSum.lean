import Mathlib

namespace Formalism.InvariantFactorPaths.KP.LL

open Finset

variable {K : Type} [Field K] [CharZero K]

noncomputable def tU (k A l : ℕ) : K :=
  (-1 : K) ^ l * ((k - 1).choose l : K) * ((A - k - l).factorial : K) / ((A - l).factorial : K)

noncomputable def tV (k A l : ℕ) : K := if l = 0 then 0 else tU k A (l - 1)

noncomputable def tT (k A l : ℕ) : K :=
  (((l.factorial : ℕ) : K) ^ 2 * (((A + 1 - l).choose l : ℕ) : K))⁻¹ *
    ((-1 : K) ^ (k - l) / ((((k - l).factorial : ℕ) : K) ^ 2 * (((A - 2 * l).choose (k - l) : ℕ) : K)))

end Formalism.InvariantFactorPaths.KP.LL
