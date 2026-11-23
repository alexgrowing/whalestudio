import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

namespace UpperTheory.GalC.Tr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem galois_admissible_of_restricted_cmDatum {D : D7} {c : CutD D} (h : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) :
    UpperTheory.GalS.AutomorphicGaloisAdmissible (cut D c).nd (cut D c).naut := fun i =>
  ⟨fun a ha π hc hr => by
    obtain ⟨ρ, c1, s, o, u, e⟩ := (h i.1).1 a ha π hc hr
    exact ⟨ρ, c1, s, fun w hw => ⟨(o w hw).dim, (o w hw).eq_of_unr, (o w hw).ine, (o w hw).mono⟩,
      fun w hw g => ⟨(u w hw g).1, (u w hw g).2.1, ⟨(u w hw g).2.2.rel.dim, (u w hw g).2.2.rel.mono, (u w hw g).2.2.rel.ine⟩,
        (u w hw g).2.2.one⟩, e⟩, (h i.1).2⟩

end UpperTheory.GalC.Tr
