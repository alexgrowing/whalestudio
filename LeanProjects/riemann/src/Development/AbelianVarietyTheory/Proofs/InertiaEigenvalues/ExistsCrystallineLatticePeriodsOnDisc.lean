import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleInvariantPeriodMatrixBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWittStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLatticeBasisMemSumDeRhamFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusLatticeGeneratorsDdRStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriodsStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedExists

theorem exists_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
    (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T),
    Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  intro l _ K bk τ hτ P AI hstd V _ _ _ _ _ _ _ ρ L _ hcrys d b
  obtain ⟨T⟩ := hstd
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  set ρm : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l] := fun g => LinearMap.toMatrix b b (actT L g) with hρm
  have hv0 := GlobalTheory.T.crystallineLattice_basis_span_invariants l K P AI T V ρ L hcrys d b
  obtain ⟨U, U', hUU', hU⟩ := GlobalTheory.T.exists_invertible_invariant_periodMatrix_bcris l K P AI T d ρm hv0
  obtain ⟨hInvB, hInvdR⟩ := GlobalTheory.T.periodRingCore_crystalline_deRham_invariants l P AI T C hC
  obtain ⟨c₁, c₃, F, F', hFF', hF⟩ := GlobalTheory.T.exists_frobeniusMatrix_crystallineModule_over_witt l K bk C hInvB d ρm U U' hUU' hU
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.bcris_periodMatrix_over_acris l K P AI T C hC bk d ρm U U' hUU' hU c₁ F hF
  have hv2 := GlobalTheory.T.crysLattice_basis_mem_sum_deRham_filtration l K P AI T V ρ L hcrys d b
  obtain ⟨N, m, k, c, β, hN, hk, hUN, hUc, hβ, hUcβ⟩ :=
    GlobalTheory.T.exists_bdRPlus_lattice_generators_ddR l K P AI T C hC hInvdR d ρm U U' hUU' hU hv2 N₀
  have hUU'ι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c₂, X, X', hXX', hnp, hX, hX'⟩ :=
    GlobalTheory.T.exists_modification_of_filtration_alt l K bk C d (U.map C.ι) (U'.map C.ι) hUU'ι N m k c β hk (fun r s => hUN r s) hUc hβ hUcβ
  obtain ⟨Z, Z', hZ⟩ := hN₀ N hN X X' hX hX'
  exact GlobalTheory.T.crystallineLatticeDiscPeriodData_of_acris_periods l K bk C τ hτ d ρm N c₁ c₂ c₃ F F' X X' hFF' hXX' hnp Z Z' hZ

end GlobalTheory.SeedExists
