import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum qvec)

namespace GlobalTheory.FinPl.Comm

theorem mainDatum_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n) : mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0}
  have h : mainDatum q χ ε P Q = ∑ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
      χ (-((ε : 𝓀[k]) * f'.1 (qvec q P))) • phiOne (ofDual P.ker f') Q := by
    funext x
    rw [mainDatum, finsum_eq_sum_of_fintype, Finset.sum_apply]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun f' _ => Submodule.smul_mem _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)

end GlobalTheory.FinPl.Comm
