import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TwoLetterLatticeGaussInverse
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ContractionOfPairingLemmas
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubCoeffP
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYDPsiMonomial
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TopLinePOf
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsP

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_of_rest (hTau : TauP) (hSm : SmithP) : QPh :=
  qPh_of hTau hSm bilinP detFactsP numP detDivP

theorem contraction_of_pairing_GL (hPh : QPh) (hCO : CartanOnto) : ContractionStandardLattice :=
  contraction_of_pairing_lemmas hPh subCoeffP subMapP subRowP lamCoeffP lamEquivP lamMulP lamEvalP lamMemP
    (subMuP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) (topLineP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) liftP detDivP intCapP hwMulP

theorem theorem_I_of_contraction (D : Formalism.BasicNotions.D7) (hQ : ContractionStandardLattice) : SecondPartClosed D :=
  theorem_I_of_two_letter_clauses_contraction D explicit_map_injective explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hQ

theorem theorem_I_of_pairing_GL (D : Formalism.BasicNotions.D7) (hPh : QPh) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, -, h0⟩ := hA 0 le_rfl
  obtain ⟨T1, -, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, -, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, -, -, -, -, hB⟩ := h2 T2 le_rfl
  have hT : AdmT D := hB.2.2.2.2
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  exact theorem_I_of_contraction D (contraction_of_pairing_GL hPh h11.2) hA

end Formalism.MainNotions.flipOneThree.Pf
