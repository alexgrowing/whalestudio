import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

namespace UpperTheory.SubgroupJ

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

def SubJ {p : ℕ} [Fact p.Prime] (D : Datum p) (w : Ideal (𝓞 D.F)) (j : ℕ) : Type :=
  {V : Submodule D.O (D.La ⧸ wSub D w 1) // Nat.card V = Ideal.absNorm w ^ (D.m * j)}

end UpperTheory.SubgroupJ
