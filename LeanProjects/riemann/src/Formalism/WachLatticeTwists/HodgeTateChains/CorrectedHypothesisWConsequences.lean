import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.FiltPow
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.UnitCongruenceGivesPerturbation
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.InjectivityPassesToCompletion
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.CycLen
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.FrobeniusPowerCongruenceHolds
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.UnitCongruenceGivesPerturbationStatement
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.GeomFact
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.CancelRight
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MapmapSubOne

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem torsion_bound_arithmetic_lemmas : MinimalExponentAttained ∧ StatCeil ∧ StatRVal ∧ StatBinom ∧ StatFiltPow ∧ StatValNN ∧ StatLL3 ∧
    StatBetaCount ∧ StatIBound ∧ StatACount ∧ StatCTBTable ∧ StatReindex ∧ StatGenM ∧ StatKappa :=
  ⟨minimal_exponent_attained, ceil, rVal, binom, filtPow, valNN, ll3, betaCount, iBound, aCount, cTBTable, reindex, genM,
    kappa⟩

theorem torsion_bound_intermediate_lemmas : InjectivityOnLayerOfPower ∧ InverseOperatorFromInjectivity ∧ InjectivityPassesToCompletion ∧ StatOnePlus ∧ PerturbationOperatorIntegral ∧ AdicPerturbationFixedFreeAndCoboundary ∧
    StatLemmaA ∧ StatEigen ∧ StatHTpoly ∧ StatEigenInj ∧ StatDevSum ∧ StatKillSum ∧ StatCores ∧
    StatTwistKill ∧ StatKill3 ∧ StatFree3 ∧ StatBKSubspace ∧ StatBKb ∧ StatBKc ∧ StatTBcB ∧ H2KilledByTateDuality ∧
    StatFreeAlg ∧ StatFreePiece ∧ StatFreeExt ∧ StatHalving ∧ StatFreeK ∧ StatIdealStep ∧ StatFiltStep ∧
    FrobeniusPowerCongruence ∧ StatNilDiv ∧ StatCharSum ∧ StatRValues :=
  ⟨t2, inverse_operator_from_injectivity, injectivity_passes_to_completion, onePlus, t3, unit_congruence_gives_perturbation, lemmaA, eigen, htpoly, eigenInj, devSum, killSum,
    cores, twistKill, kill3, free3, bkSubspace, bkb, bkc, tbcB, h2_killed_by_tate_duality, freeAlg, freePiece, freeExt,
    halving, freeK, idealStep, filtStep, frobenius_power_congruence_holds, nilDiv, charSum, rValues⟩

theorem hypothesis_W_sandwich_consequences : StatLemmaAMat ∧ StatSandwichAA ∧ StatSandwichOC ∧ StatWSandwich ∧ GammaIterateMatrixCongruence ∧
    StatTwistUm ∧ UnitCongruenceGivesPerturbation :=
  ⟨lemmaAMat, sandwichAA, sandwichOC, wSandwich, w3Um, twistUm, unitCongruenceGivesPerturbation_statement⟩

theorem corrected_hypothesis_W_consequences : StatHypWComm ∧ StatWSandwich' ∧ StatWFix ∧ StatWCocycle ∧ StatWGam ∧ StatWUm ∧ StatWEnd :=
  ⟨hypWComm, wSandwich', wFix, wCocycle, wGam, wUm, wEnd⟩

theorem galois_action_on_module_D : StatWActU ∧ StatWAct ∧ StatXNzd ∧ StatWChain ∧ StatWD := ⟨wActU, wAct, xNzd, wChain, wD⟩

theorem free_part_over_cyclotomic_group : StatFreeGm' ∧ StatFreeKTop := ⟨freeGm', freeKTop⟩

theorem free_part_H0_and_TB_theorems : StatPiece ∧ StatLL ∧ StatFreeGm ∧ InvariantsKilledByPower ∧ InvariantsLengthBound ∧ StatTB ∧ StatTBFull ∧
    StatTBLen ∧ StatTopsAtM :=
  ⟨piece, ll, freeGm, h0, H0_length_bound_holds, tb, tbFull, tbLen, topsAtM⟩

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
