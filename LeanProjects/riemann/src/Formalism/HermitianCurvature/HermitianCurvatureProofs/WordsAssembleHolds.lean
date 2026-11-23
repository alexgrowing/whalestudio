import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferMatrixFactorization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem words_assemble_holds : Formalism.FourierDecayAlt.Wd.WordsAssemble := by
  intro _hInsMul hInsStar _hInsDiag hInsFree _hSlotP _hSlotM hStart _hExchP _hExchM hLetP hLetM hWF
    hTTF hE1 hE2 hE3 hE4 hXp hXm _hVecA _hVecB hDualP hDualM _hRhUU _hRhtUU
  have hWM : WordModule := Wd5.wordModule_of hStart hLetP hLetM hWF
  exact ⟨hWM, wd_siteStep_of hE1 hE2 hE3 hE4, word_matrix_entry_one,
    Wd8.cwEigen_of hE1 hE2 hXp hXm hTTF, Wd8.uwProduct,
    Wd10.dualityList_of hInsFree hInsStar hWF hWM hDualP hDualM, kappa_formula_holds,
    plane_wave_vector_identity, plane_wave_word_identity⟩

end Formalism.FourierDecayAlt.P
