import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.BlockValuationRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.CongruenceNumberUnitaryThreeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.PropGKU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.OneCharU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.IntOfNorm

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.Z.J

open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W

theorem countI (hH : Af.HypothesesH) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : Z.Kato.KatoTwo) (hU : LinkedUnl) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  have hC := Core0.cohInp hH.litN hK
  have hE := unlEnd3 hU
  U3.countI (U3.corGK (propGKU (congruenceNumberUnitaryThree_of hH.toClassicalTheorems)
    (oneCharU hC Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP hKa (rigIU hC hH (DescentVanishingReductions.adL hH) hE)
      (Th.rigII hC hH (DescentVanishingReductions.adL hH)) (admissible_unitary_of_inputs hC hH hE) h3)))

end UpperTheory.V.Z.J
