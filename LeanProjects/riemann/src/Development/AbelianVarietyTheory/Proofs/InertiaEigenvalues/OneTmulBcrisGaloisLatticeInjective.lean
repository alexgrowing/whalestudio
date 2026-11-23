import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TContInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, -, -⟩ := GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  haveI : Nontrivial (Per.BdR l) := ⟨(GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.exists_pair_ne⟩
  exact ι.domain_nontrivial

theorem zl_bcris_injective (l : ℕ) [Fact l.Prime] : Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  haveI := bcris_nontrivial l
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) z) := by
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]
    exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)
  exact hu.ne_zero hz

theorem includeLeft_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (zl_bcris_injective l)
  intro x y hxy
  apply (TensorProduct.rid ℤ_[l] O).symm.injective
  apply h
  simpa [Algebra.TensorProduct.algebraMap_apply] using hxy

theorem one_tmul_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] :
    Function.Injective (fun x : M => (1 : OB l O) ⊗ₜ[O] x) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap O (OB l O)) (includeLeft_injective l O)
  intro x y hxy
  apply (TensorProduct.lid O M).symm.injective
  apply h
  simpa [← Algebra.TensorProduct.one_def] using hxy

end GlobalTheory.TContInj

theorem GlobalTheory.TContInj.main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  intro l _ LL T
  haveI : Module.Free (↥(OL LL)) ↥T.L.T := T.L.free
  exact GlobalTheory.TContInj.one_tmul_injective l ↥(OL LL) ↥T.L.T
