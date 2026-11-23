import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExt
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJump_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  first | exact @GlobalTheory.Per.JumpRestrict.jump_restrict | exact GlobalTheory.Per.JumpRestrict.jump_restrict | (intros; apply GlobalTheory.Per.JumpRestrict.jump_restrict <;> assumption)
