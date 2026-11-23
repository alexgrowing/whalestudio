import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfLeaves
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.VwinOf

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.DescentVanishingReductions

open UpperTheory.V.Lit UpperTheory.V.W

theorem adL (hH : Af.HypothesesH) : Th.AdL := Th.adL hH (cohP hH.litN)

theorem countI (hH : Af.HypothesesH) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : Z.Kato.KatoTwo) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  have hC := Core0.cohInp hH.litN hK
  Th.caseI
    { toCohInp := hC, lemM := Alg.M.main_holds, lemM' := Alg.M.mprime_holds, lemP := Alg.lemmaP, kato := hKa,
      rigI := Th.rigI hC hH (adL hH), rigII := Th.rigII hC hH (adL hH), number := Af.numberU3_of_admissible hH.toClassicalTheorems } h3

end UpperTheory.V.HV.DescentVanishingReductions
