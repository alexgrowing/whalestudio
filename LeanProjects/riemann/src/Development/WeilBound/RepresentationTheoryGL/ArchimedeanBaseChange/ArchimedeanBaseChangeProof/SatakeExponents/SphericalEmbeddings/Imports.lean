import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExpEmb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ValuationDetKO
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GaloisFixedAdelicMatricesDescend
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.InjectiveOfIrred
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2SphericalSwap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.UniqSub

namespace PositivityTheory.Rg.BcB.N3.Final

open PositivityTheory.Rg.BcB.N3

theorem n3 : N3 :=
  Pee.galois_fixed_adelic_matrices_descend (fun k _ _ _ _ => Pee.expEmb k)
    (fun k _ _ _ _ => Pee.extremeSph_of k (Pee.sphConst k) (Pse.sphEmb k) (Pus.uniqSub k)) Psl.satLink

end PositivityTheory.Rg.BcB.N3.Final
