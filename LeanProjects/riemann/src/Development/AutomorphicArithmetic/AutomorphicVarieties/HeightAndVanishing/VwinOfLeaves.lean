import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ResidualAutomorphyOfLinkedEnds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TopTheorem.NumberU3OfAdmissible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.RigIIOfHypotheses

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.Core0

open UpperTheory.V.Lit

theorem cohInp (hN : LitN) (hK : ∃ CK : ℝ, LemmaK CK) : U3.CohInp :=
  ⟨U.localGaloisCohomology₂ hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hK⟩

theorem rigII (hN : LitN) (hK : ∃ CK : ℝ, LemmaK CK) (adQ : Af.AdVanishQ) (nw : Af.NewformAut) (hKa : Z.Kato.KatoTwo) : Z.Kato.RigII :=
  Z.Kato.rigII_of (cohInp hN hK) adQ nw hKa

theorem countI (hN : LitN) (hK : ∃ CK : ℝ, LemmaK CK) (hR : Z.Kato.RigII) (adK : Af.AdVanishK) (nU : Af.CongruenceNumberRankThree)
    (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  Z.Kato.caseI
    { toCohInp := cohInp hN hK, lemM := Alg.M.main_holds, lemM' := Alg.M.mprime_holds, lemP := Alg.lemmaP, rigII := hR, adK := adK,
      number := nU } h3

end UpperTheory.V.HV.Core0
