import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

namespace UpperTheory.Gal.TranscendenceTraces

theorem adic : Adic := adic_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance

theorem all_holds : Weights ∧ Torsion ∧ Adic := ⟨weights_holds, torsion_holds, adic⟩

end UpperTheory.Gal.TranscendenceTraces
