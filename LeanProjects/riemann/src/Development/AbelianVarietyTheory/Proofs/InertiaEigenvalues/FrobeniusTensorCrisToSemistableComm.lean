import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiV_crisIncl_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  intro l _ P K V _ _ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [crisIncl_tmul, phiV_tmul, phiSt_C, φVB, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, P.PD_φ K b]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.PMon
