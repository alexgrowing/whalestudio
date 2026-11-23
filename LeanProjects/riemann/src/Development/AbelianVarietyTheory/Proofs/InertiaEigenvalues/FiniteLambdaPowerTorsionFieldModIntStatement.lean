import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModInt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)), Irreducible lam → ∀ a : ℕ, Finite ↥(Xq ↥LL.1 lam a) := by
  first | exact @GlobalTheory.UseLoc.Cases.finite_Xq | exact GlobalTheory.UseLoc.Cases.finite_Xq | (intros; apply GlobalTheory.UseLoc.Cases.finite_Xq <;> assumption)
