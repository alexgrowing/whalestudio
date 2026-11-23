import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FilStable

theorem ι_σB {l : ℕ} [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (g : Per.Gq l) (β : Per.Bcris l) :
    C.ι (Per.σB g β) = Per.σD g (C.ι β) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := C.ι.comp (Per.σB g)) (g := (Per.σD g).comp C.ι) fun x => ?_) β
  have h1 : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (GlobalTheory.MemLoc.sigA g x) :=
    GlobalTheory.CrisMaps.σB_sigA g x
  change C.ι (Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x)) =
    Per.σD g (C.ι (algebraMap (Per.Acris l) (Per.Bcris l) x))
  rw [h1, C.ι_j, C.ι_j, GlobalTheory.MemLoc.FilLaws.σD_alg, GlobalTheory.MemLoc.CrisUnique.equivariant C.j_cris]

theorem fil_zero_stable : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (C : GlobalTheory.MemLoc.Core l), ∀ v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}, actB (sQ l) T g v ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g C v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨β, x, hβ, rfl⟩ := hw
    refine Submodule.subset_span ⟨Per.σB (sQ l g) β, T.actT g x, ?_, ?_⟩
    rotate_left 1
    · simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, galOB,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    · rw [ι_σB]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.1 _ 0 _ hβ
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BKGal.FilStable
