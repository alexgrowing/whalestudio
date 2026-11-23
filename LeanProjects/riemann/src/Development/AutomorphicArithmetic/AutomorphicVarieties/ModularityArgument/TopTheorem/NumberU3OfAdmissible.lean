import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.VwinOfInputs

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy UpperTheory.V.HV

namespace UpperTheory.V.Z.Top

structure Leaves : Prop where
  aut3G : Aut.AutomorphyUnramifiedCoefficients
  s6 : Aut.AutomorphyClauseStatement
  sp4 : Aut.Sp4In
  numberU3_of_admissible : Af.CongruenceNumberRankThree
  numberSp4 : Af.NumberSp4
  adK : Af.AdVanishK
  adQ : Af.AdVanishQ
  newAut : Af.NewformAut
  kato : Lit.KatoUseN
  lemK : ∃ CK : ℝ, LemmaK CK

end UpperTheory.V.Z.Top
