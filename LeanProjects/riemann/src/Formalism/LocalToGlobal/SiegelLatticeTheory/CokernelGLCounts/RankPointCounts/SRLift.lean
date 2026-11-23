import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossTranspose

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def SRLift : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R)
    (K : Submodule M.R (Fin (n + 1) → M.R)),
    (∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0) →
    (∀ v : Fin (n + 1) → M.R, ∃ x, v - A.mulVec x ∈ K) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
