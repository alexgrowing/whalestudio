import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def qU : ℝ := ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) : NNReal) : ℝ)

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lam1 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ s : ℝ) : ℂ) * Complex.I ^ (s - 2)

def lam2 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ (s - 1) : ℝ) : ℂ) * Complex.I ^ (s - 1)

def omN (S : C.HidaSetting E Wp Wq) (N : ℕ) (P : C.LPt) : ℝ :=
  √(PBL.nnS S P) / PBL.bS S P * √(Top.wPt (S.T * S.T') S.G.r (PBL.stdS S P) ^ N)

end pts

end

end Formalism.FourierDecayAlt.P.GermRateSplit
