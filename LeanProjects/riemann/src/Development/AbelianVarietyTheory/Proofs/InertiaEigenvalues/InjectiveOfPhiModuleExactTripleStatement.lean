import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTriple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_phiModule_exact_triple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  first | exact @GlobalTheory.BK.IsExactTriple.injective_app | exact GlobalTheory.BK.IsExactTriple.injective_app | (intros; apply GlobalTheory.BK.IsExactTriple.injective_app <;> assumption)
