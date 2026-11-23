import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPow
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  first | exact @GlobalTheory.LimCocycle.limit_cocycle | exact GlobalTheory.LimCocycle.limit_cocycle | (intros; apply GlobalTheory.LimCocycle.limit_cocycle <;> assumption)
