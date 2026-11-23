import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  first | exact @GlobalTheory.Per.LetterDim.tied_letter_component_finrank | exact GlobalTheory.Per.LetterDim.tied_letter_component_finrank | (intros; apply GlobalTheory.Per.LetterDim.tied_letter_component_finrank <;> assumption)
