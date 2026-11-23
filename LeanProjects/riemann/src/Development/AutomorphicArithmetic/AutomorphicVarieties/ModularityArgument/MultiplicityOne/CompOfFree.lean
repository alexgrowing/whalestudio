import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockSA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT

open UpperTheory.V.Z.Tf UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.V.Z.Mult

theorem noData_free : NoData := fun _ _ _ _ hE _ hn _ π _ hd D h1 h2 _ h4 => h1 (SR.has_of_split hE hn π hd D h2 h4)

theorem compOf_free : CompOf := fun E _ _ _ hE n hn _ π _ hd σ hσ hun hae =>
  (UpperTheory.Gal.Desc.match_of UpperTheory.Gal.Desc.speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
    PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin hE hn π (GOne.unitOf E n hn π hd) σ hσ hun hae).3

theorem mult_free : Mult :=
  have hA := rCountAt compOf_free evalD cpUniq Asm.places
  rMult (rIdent noData_free hA geomTr UpperTheory.ConvolutionTheory.G2.g2s UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      (endoS (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor unitary_one_characters_separated_by_eigenvalues Asm.places) Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)) stableBlockSA)
    hA levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
