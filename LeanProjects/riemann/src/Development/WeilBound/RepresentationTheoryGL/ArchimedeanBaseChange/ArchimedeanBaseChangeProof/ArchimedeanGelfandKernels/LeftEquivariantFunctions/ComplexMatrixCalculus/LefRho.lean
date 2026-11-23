import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Fr0Laws

noncomputable section

namespace PositivityTheory.RgBcC

def lefRho (n : ℕ) (lam : Fin n → ℤ) : Matrix.unitaryGroup (Fin n) ℂ →* (EV n lam →L[ℂ] EV n lam) where
  toFun k := lefFr n lam k.1
  map_one' := frOne n lam
  map_mul' k k' := frMulK n lam k k'

def lefE (n : ℕ) (lam : Fin n → ℤ) : KMod n where
  V := EV n lam
  ρ := lefRho n lam
  iso := frIso n lam
  cont := frCont n lam

end PositivityTheory.RgBcC
