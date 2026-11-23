import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open scoped Pointwise

namespace GlobalTheory.BKGal.ContNear

theorem sub_mem_pow_smul_lattice_eventually :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (t : T.V), t ∈ T.L.T → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : ↥LL.1) ^ m) • t' := by
  intro l _ LL T t _ m
  have hO := GlobalTheory.HTW.Rec.goodO_finExt_integers l LL
  have hT : IsOpen (T.L.T : Set T.V) := GlobalTheory.Cyc.locLat_isOpen hO T
  have hc : ((l : ↥LL.1) ^ m) ≠ 0 := by
    refine pow_ne_zero _ ?_
    have h1 : (l : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by simp
    rw [h1, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hU : IsOpen (((l : ↥LL.1) ^ m) • (T.L.T : Set T.V)) := hT.smul₀ hc
  haveI := hO.2.2.2.1
  haveI := IsModuleTopology.topologicalAddGroup (↥LL.1) T.V
  have hf : Continuous fun g : Gl l => T.ρ g t - t := (T.cont t).sub continuous_const
  have h0 : (fun g : Gl l => T.ρ g t - t) 1 ∈ ((l : ↥LL.1) ^ m) • (T.L.T : Set T.V) := by
    simp only [map_one, Module.End.one_apply, sub_self]
    exact ⟨0, T.L.T.zero_mem, smul_zero _⟩
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with g hg
  obtain ⟨t', ht', he⟩ := hg
  exact ⟨t', ht', he.symm⟩

end GlobalTheory.BKGal.ContNear
