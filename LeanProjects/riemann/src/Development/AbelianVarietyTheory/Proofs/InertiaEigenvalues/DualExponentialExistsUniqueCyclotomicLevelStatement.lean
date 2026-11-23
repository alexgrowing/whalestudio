import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialExistsUniqueCyclotomicLevel
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExponential_existsUnique_cyclotomicLevel : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, (∀ z : GQ l → ℚ_[l], CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z → ∃ α ∈ Ks K s, ExpStar D.loc (Gj K s) e z α) ∧ ∀ (z : GQ l → ℚ_[l]) (α α' : Om l), α ∈ Ks K s → α' ∈ Ks K s → ExpStar D.loc (Gj K s) e z α → ExpStar D.loc (Gj K s) e z α' → α = α' := by
  first | exact @GlobalTheory.ExpDef.expStar_existsUnique | exact GlobalTheory.ExpDef.expStar_existsUnique | (intros; apply GlobalTheory.ExpDef.expStar_existsUnique <;> assumption)
