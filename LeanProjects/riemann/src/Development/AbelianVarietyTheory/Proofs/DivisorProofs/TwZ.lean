import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.KumPic

abbrev twZ (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def dv (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ (twZ q)).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

end GlobalTheory.EtC.KumPic

end
