import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SymZeroCommFrameMatrix

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def TDOf : Prop := Avg → HbOrtho → SwapLaws → MatrixFrechetDerivativeAtZero → WedgeDer → ∀ (n : ℕ) (lam : Fin n → ℤ),
  lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
    -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam)

def EigOf : Prop := Avg → GamMul → RmLaws → RmHol → RmAnti → EigProd → EigLocal → ∀ (n : ℕ) (lam : Fin n → ℤ),
  Antitone lam → ∀ w : EV n lam, IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w)

end PositivityTheory.RgBcC
