import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrimeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
