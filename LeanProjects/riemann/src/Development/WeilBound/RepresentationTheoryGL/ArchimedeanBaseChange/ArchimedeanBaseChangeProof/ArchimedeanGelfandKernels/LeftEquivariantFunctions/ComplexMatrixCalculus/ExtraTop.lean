import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DiagInvEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.MultiDiagonalTraces.GamTrace

namespace PositivityTheory.RgBcC

theorem isLefK_model {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) : Real.IsLefK lam (lefE n lam) (lefT n lam) :=
  isLefK_of gamTrace hlam

end PositivityTheory.RgBcC
