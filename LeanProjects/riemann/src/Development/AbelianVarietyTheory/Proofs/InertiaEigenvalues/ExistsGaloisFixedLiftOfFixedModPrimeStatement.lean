import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixedLiftOfFixedModPrime
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) (x : RW LL), (∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) → ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | exact GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | (intros; apply GlobalTheory.Decompl.exists_fix_lift_of_fix_mod <;> assumption)
