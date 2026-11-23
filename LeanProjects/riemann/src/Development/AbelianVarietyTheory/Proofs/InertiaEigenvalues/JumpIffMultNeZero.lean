import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpMult

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_ddR (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ a ≤ DdR PD ρ :=
  le_trans inf_le_left inf_le_left

theorem jump_iff_of_finite [FiniteDimensional LL ↥(DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FiniteDimensional LL ↥(FildR PD ρ τ a) ∧ 0 ≤ multV PD ρ τ a ∧
      (IsJumpV PD ρ τ a ↔ multV PD ρ τ a ≠ 0) := by
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_ddR PD ρ τ a)
  have hle := fildR_succ_le PD ρ τ a
  refine ⟨this, ?_, ?_, ?_⟩
  · have := Submodule.finrank_mono hle
    unfold multV
    omega
  · intro hj h0
    apply hj
    apply Submodule.eq_of_le_of_finrank_eq hle
    unfold multV at h0
    omega
  · intro h h'
    exact h (by rw [multV, h', sub_self])

end General

theorem jump_iff_mult_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) ρ τ a) ∧ 0 ≤ multV (P.PD K) ρ τ a ∧ (IsJumpV (P.PD K) ρ τ a ↔ multV (P.PD K) ρ τ a ≠ 0) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ a
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact jump_iff_of_finite (P.PD K) ρ τ a

end GlobalTheory.Per.JumpMult
