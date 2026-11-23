import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulEqTmulOfFrobeniusFixedFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryFrobeniusFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionSubMemFiltrationZeroOfMonodromyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem coboundary_mem_lattice_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hy hMon b hb g hg
  obtain ⟨C, hC⟩ := GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy l a e O K t ϖ hl2 ι η H D T R y hy hMon b hb g hg
  exact GlobalTheory.T.exists_prime_pow_smul_eq_tmul_of_frobenius_fixed_fil_zero hF l O K (Gl l) T C _ (GlobalTheory.T.galoisCoboundary_frobenius_fixed l a e O K t ϖ ι η H D T R y hy b hb g hg) hC

end GlobalTheory.BKGal
