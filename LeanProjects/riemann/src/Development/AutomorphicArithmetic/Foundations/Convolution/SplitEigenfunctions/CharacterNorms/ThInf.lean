import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.TA

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def thInf (D : Dat ℚ E) : Cinf E := pInf E (rt D.θ)

def nC (z : Cinf E) : GL (Fin 2) (Cinf E) :=
  ⟨!![1, z; 0, 1], !![1, -z; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def kInf (k : GL (Fin 2) (A E)) : GL (Fin 2) (Cinf E) := Matrix.GeneralLinearGroup.map (pInf E) k

def cv (D : Dat ℚ E) (k : GL (Fin 2) (A E)) (t : ℝ) : GL (Fin 2) (Cinf E) :=
  (kInf k)⁻¹ * nC (t • thInf D) * kInf k

def XB (D : Dat ℚ E) (k : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (Cinf E) :=
  ((kInf k)⁻¹).val * !![0, thInf D; 0, 0] * (kInf k).val

end UpperTheory.ConvolutionTheory.RankTwoDescent.TA

end
