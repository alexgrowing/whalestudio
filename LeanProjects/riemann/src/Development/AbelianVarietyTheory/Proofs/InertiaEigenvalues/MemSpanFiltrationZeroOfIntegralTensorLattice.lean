import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

section IntegralSpan

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_filD_zero : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
  have h0 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, ← map_one (algebraMap (Per.AinfP l) (Per.BdRp l)),
      GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    simp
  have h1 := GlobalTheory.RingIface.alg_mem_FilD_nat l h0
  rwa [map_one, Nat.cast_zero] at h1

theorem algebraMap_mem_filD_zero (u : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filD_zero

theorem equivFinsuppOfBasisLeft_map_id {O B B' ι : Type} [CommRing O] [Algebra ℤ_[l] O]
    [CommRing B] [CommRing B'] [Algebra ℤ_[l] B] [Algebra ℤ_[l] B']
    [DecidableEq ι] (b : Module.Basis ι ℤ_[l] O) (g : B →ₐ[ℤ_[l]] B') (r : O ⊗[ℤ_[l]] B) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (Algebra.TensorProduct.map (AlgHom.id O O) g r) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b r k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul o β => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem equivFinsuppOfBasisRight_map_id {O R R' M κ : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M]
    [DecidableEq κ] (b : Module.Basis κ O M) (f : R →ₐ[O] R') (w : R ⊗[O] M) (j : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f.toLinearMap LinearMap.id w) j =
      f (TensorProduct.equivFinsuppOfBasisRight b w j) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem mem_span_filD_zero_of_iotaO_eq {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (r : OB l O) (s : OD l O) (h : iotaO O C r = dRO l O s) :
    r ∈ Submodule.span O
      {u : OB l O | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l 0 ∧ u = (1 : O) ⊗ₜ[ℤ_[l]] β} := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hr : r = (TensorProduct.equivFinsuppOfBasisLeft b r).sum fun k β => b k ⊗ₜ[ℤ_[l]] β := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hr, Finsupp.sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) ∈ Per.FilD l 0 := by
    have h1 := equivFinsuppOfBasisLeft_map_id b (iotaZ C) r k
    have h2 := equivFinsuppOfBasisLeft_map_id b (bdRpToBdR l) s k
    have h3 : Algebra.TensorProduct.map (AlgHom.id O O) (iotaZ C) r =
        Algebra.TensorProduct.map (AlgHom.id O O) (bdRpToBdR l) s := h
    rw [h3, h2] at h1
    have h4 : C.ι (TensorProduct.equivFinsuppOfBasisLeft b r k) =
        algebraMap (Per.BdRp l) (Per.BdR l) (TensorProduct.equivFinsuppOfBasisLeft b s k) := h1.symm
    rw [h4]
    exact algebraMap_mem_filD_zero _
  have h5 : b k ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k) =
      b k • ((1 : O) ⊗ₜ[ℤ_[l]] (TensorProduct.equivFinsuppOfBasisLeft b r k)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hk, rfl⟩)

end IntegralSpan

theorem mem_span_filD_zero_of_integral : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
    (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T),
    TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) →
      w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T),
        C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ O K _ _ _ _ _ _ _ T C w hw
  classical
  obtain ⟨z, hz⟩ := hw
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  have hw' : w = (TensorProduct.equivFinsuppOfBasisRight bT w).sum fun j r => r ⊗ₜ[O] bT j := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hw', Finsupp.sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : iotaO O C (TensorProduct.equivFinsuppOfBasisRight bT w j) =
      dRO l O (TensorProduct.equivFinsuppOfBasisRight bT z j) := by
    rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
    exact (congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) hz).symm
  have hr := mem_span_filD_zero_of_iotaO_eq C _ _ hj
  have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk O (OB l O) ↥T.L.T).flip (bT j)) hr
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨u, ⟨β, hβ, rfl⟩, rfl⟩
  exact ⟨β, bT j, hβ, rfl⟩

end GlobalTheory.BKGal.HatVal
