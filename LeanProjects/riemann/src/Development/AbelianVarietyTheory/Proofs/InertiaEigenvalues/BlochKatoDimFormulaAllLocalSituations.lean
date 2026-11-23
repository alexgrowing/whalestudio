import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem blochKatoDim_at_every_local_situation : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  intro D l _ K LL _
  exact GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory
