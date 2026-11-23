import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilTStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantLatticeFiltrationZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalIBSubMemFilOStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinatesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in

theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by
    rw [GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine GlobalTheory.T.galOB_iB_sub_iB_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (GlobalTheory.T.jB_single_mem_filT' l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
