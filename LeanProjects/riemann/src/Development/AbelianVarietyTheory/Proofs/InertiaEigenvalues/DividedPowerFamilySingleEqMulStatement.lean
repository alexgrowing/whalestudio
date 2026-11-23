import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerFamily_single_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  first | exact @GlobalTheory.CrysPrism.ofW_single | exact GlobalTheory.CrysPrism.ofW_single | (intros; apply GlobalTheory.CrysPrism.ofW_single <;> assumption)
