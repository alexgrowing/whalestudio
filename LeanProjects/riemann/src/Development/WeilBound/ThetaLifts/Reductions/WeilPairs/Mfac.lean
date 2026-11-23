import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ModulusFactorDefinition

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

def mfac (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nT : ℕ} (nS : ℕ)
    (t : GL (Fin nT) (AF F ⊗[F] E)) : ℝ :=
  (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ)

end PositivityTheory.ThKW.ModulusFactorDefinition

end
