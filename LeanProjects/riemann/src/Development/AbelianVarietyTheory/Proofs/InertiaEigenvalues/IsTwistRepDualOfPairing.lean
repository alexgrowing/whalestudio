import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedIsCrysDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShiftStatement
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualOne

theorem isTwistRep_dual_of_pairing {G L : Type} [Group G] [Field L]
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {V' : Type} [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']
    (ρ : Representation L G V) (ρ' : Representation L G V') (χ : G →* Lˣ)
    (m : V →ₗ[L] V' →ₗ[L] L)
    (h1 : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : Lˣ) : L) * m x y)
    (h2 : ∀ y, (∀ x, m x y = 0) → y = 0) (h3 : finrank L V = finrank L V') :
    IsTwistRep χ ρ.dual ρ' := by
  have hinj : Function.Injective m.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => by simpa using LinearMap.congr_fun hy x
  have hdim : finrank L V' = finrank L (Module.Dual L V) := by
    rw [Subspace.dual_finrank_eq, h3]
  let f : V' ≃ₗ[L] Module.Dual L V := m.flip.linearEquivOfInjective hinj hdim
  have hf : ∀ y x, f y x = m x y := fun y x => rfl
  refine ⟨f.symm, fun g φ => ?_⟩
  obtain ⟨y, rfl⟩ := f.surjective φ
  apply f.injective
  rw [map_smul, f.apply_symm_apply, f.symm_apply_apply]
  ext x
  have hx : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := h1 g (ρ g⁻¹ x) y
  rw [hx] at this
  rw [hf, this, LinearMap.smul_apply, Representation.dual_apply, smul_eq_mul]
  congr 1

theorem isCrys_of_isDual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) ρ ρ' m → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' := by
  intro l _ P AI hT K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m hD hρ
  obtain ⟨h1, -, h2, h3⟩ := hD
  have htw := isTwistRep_dual_of_pairing ρ ρ' _ m h1 h2 h3
  have hreg := (GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT).1
  have hdual := GlobalTheory.Per.TiedDual.tied_isCrys_dual l P AI hT hreg K LL V ρ hρ
  have hcyc := (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI hT K LL 1).1
  rw [zpow_one] at hcyc
  exact (GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift l P AI hT K LL _ ρ.dual V' ρ' _ htw hcyc hdual).1

end GlobalTheory.DualOne
