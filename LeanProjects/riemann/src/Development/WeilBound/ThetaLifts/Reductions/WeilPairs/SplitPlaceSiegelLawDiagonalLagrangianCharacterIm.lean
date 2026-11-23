import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsAlt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.WeilDatumDoubledTargetSiegelRuleImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ThetaFunctionHeisenbergInvariant
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsMore
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def dC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)

variable (F E) in

def aC (n : ℕ) : Matrix (Fin (n + n)) (Fin n) (AF F ⊗[F] E) :=
  ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (-1)).submatrix finSumFinEquiv.symm id)

def prof (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) (y : WOF F E nS nT) : ℂ :=
  GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
    (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ (aC F E nT * y) f)

end GlobalTheory.SplitLagrF

end
