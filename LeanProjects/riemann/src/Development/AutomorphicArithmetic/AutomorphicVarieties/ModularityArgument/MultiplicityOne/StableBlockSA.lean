import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.NoDataOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableGA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableSA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.AbsCoreA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.OfLitN

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem stableBlockSA : StableBlockSA :=
  stableSA (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places
    (stableGA Pi.piFin_holds Pi.piAdm_pf Pi.growthPiJ_holds (UpperTheory.Zero.ConvolutionTheory.EB.cmbPiA piTermA Pi.twTrSum_pf) cuspReadI)

theorem mult (hW : GalWeak 4) : Mult := mult_of hW (compOf' hW) stableBlockSA

theorem mult_of_litN (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) : Mult := mult (galWeak_of_litN P 4)

end UpperTheory.V.Z.Mult
