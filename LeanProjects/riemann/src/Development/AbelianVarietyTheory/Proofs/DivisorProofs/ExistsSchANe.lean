import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.SWLit

namespace GlobalTheory.SiegelCoefTheta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def antiPt (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) (x : κ → AF F) :
    Matrix (Fin m) (Fin (n + n)) (AE F E) :=
  co.e.symm (x, 0)

def coefChar (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) (ψ : AddChar (AF F) ℂ)
    (x : κ → AF F) (b : UA σ J₂) : ℂ :=
  ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂) (antiPt co x * (mat b)ᵀ) (antiPt co x))

variable (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ)

variable {co}

end GlobalTheory.SiegelCoefTheta
