import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LemmaA2indepOf
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathBasisOfCount
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.GoodWOfWeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.FactSplit

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem psiWeight : PsiWeight := psi_weight
theorem fact_index_weights : IndexWeightsDominance := index_weights_dominance
theorem polBRank : PolBRank := polynomial_b_rank
theorem pathIdxFinite : PathIdxFinite := path_index_finite
theorem factBrk : FactBrk := fact_break
theorem factEV : FactEV := factEV_of fact_index_weights psiWeight
theorem lemmaA2indep : LemmaA2indep := lemmaA2indep_of factEV factBrk
theorem path_basis_theorem : PathBasisOfCount := path_basis_of_count lemmaA2indep pathIdxFinite polBRank

theorem psiPath_basis (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (R : Type) [CommRing R] :
    LinearIndependent R (fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) ∧
      Submodule.span R (Set.range fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) =
        polB R n N B := path_basis_theorem n N isVec B (countPAll n N isVec B) R
theorem factSplit : FactSplit := factSplit_valid

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
