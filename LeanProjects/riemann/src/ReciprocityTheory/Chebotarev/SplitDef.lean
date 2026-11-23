import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

noncomputable def under {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : Prm E where
  asIdeal := P.asIdeal.under (𝓞 E)
  isPrime := Ideal.IsPrime.under _ _
  ne_bot := Ideal.under_ne_bot (𝓞 E) P.ne_bot

theorem under_asIdeal {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : (under (E := E) P).asIdeal = P.asIdeal.under (𝓞 E) := rfl

end ReciprocityTheory.Cheb
