import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

variable {l : ℕ} [Fact l.Prime]

theorem FilD_anti {a b : ℤ} (h : a ≤ b) : Per.FilD l b ≤ Per.FilD l a := by
  obtain ⟨k, rfl⟩ := Int.le.dest h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans ?_ ih
    have := (GlobalTheory.MemLoc.filD_laws l).1 (a + k)
    simpa [add_assoc] using this

theorem alg_mem_FilD_iff (n : ℕ) (y : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n :=
  (GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 n y

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {β : Per.Bcris l} (h : C.ι β ∈ Per.FilD l n) :
    (1 : O) ⊗ₜ[ℤ_[l]] β ∈ filO O C n :=
  Submodule.subset_span ⟨β, h, rfl⟩

theorem filO_anti {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} (h : a ≤ b) : filO O C b ≤ filO O C a :=
  Submodule.span_mono fun _ ⟨β, hβ, hx⟩ => ⟨β, FilD_anti h hβ, hx⟩

theorem mul_mem_filO {C : GlobalTheory.MemLoc.Core l} {a b : ℤ} {x y : OB l O} (hx : x ∈ filO O C a)
    (hy : y ∈ filO O C b) : x * y ∈ filO O C (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨β', hβ', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      refine tmul_mem_filO ?_
      rw [map_mul]
      exact (GlobalTheory.MemLoc.filD_laws l).2.2.1 a b _ _ hβ hβ'
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul o y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul o x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o h

theorem toOB_tmul_mem_filO {C : GlobalTheory.MemLoc.Core l} {n : ℕ} {c : Per.Acris l} (h : C.j c ∈ Per.FilP l n) :
    toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] c) ∈ filO O C n := by
  refine tmul_mem_filO ?_
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) c) ∈ _
  rw [C.ι_j]
  exact (alg_mem_FilD_iff n _).2 h

theorem toOB_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul o c =>
    have : (o ⊗ₜ[ℤ_[l]] c : OCr l O) = o • ((1 : O) ⊗ₜ[ℤ_[l]] c) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ o (toOB_tmul_mem_filO (n := 0) (GlobalTheory.BdRQuot.mem_filtration_zero _))
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem isUnit_l_BdRp : IsUnit (l : Per.BdRp l) := by
  refine (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ ?_
  rw [map_natCast]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem mem_filO_of_pow_mul {C : GlobalTheory.MemLoc.Core l} {n : ℤ} {s : ℕ} {x : OB l O}
    (h : (l : OB l O) ^ s * x ∈ filO O C n) : x ∈ filO O C n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_right_inv
  have hι : C.ι u ∈ Per.FilD l 0 := by
    obtain ⟨v, hv⟩ := (isUnit_l_BdRp (l := l)).exists_right_inv
    have h1 : C.ι u = algebraMap (Per.BdRp l) (Per.BdR l) v := by
      have h2 : C.ι (l : Per.Bcris l) * C.ι u = 1 := by rw [← map_mul, hu, map_one]
      have h3 : (algebraMap (Per.BdRp l) (Per.BdR l) (l : Per.BdRp l)) * algebraMap _ _ v = 1 := by
        rw [← map_mul, hv, map_one]
      rw [map_natCast] at h2
      rw [map_natCast] at h3
      calc C.ι u = (algebraMap (Per.BdRp l) (Per.BdR l) v * (l : Per.BdR l)) * C.ι u := by
            rw [mul_comm (algebraMap _ _ v), h3, one_mul]
        _ = _ := by rw [mul_assoc, h2, mul_one]
    rw [h1]
    exact (mem_FilD_zero_iff _).2 ⟨v, rfl⟩
  have hU : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s ∈ filO O C 0 := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    refine tmul_mem_filO ?_
    rw [map_pow]
    have hk : ∀ k : ℕ, C.ι u ^ k ∈ Per.FilD l 0 := fun k => by
      induction k with
      | zero => rw [pow_zero]; exact (GlobalTheory.MemLoc.filD_laws l).2.1
      | succ k ih => rw [pow_succ]; simpa using (GlobalTheory.MemLoc.filD_laws l).2.2.1 0 0 _ _ ih hι
    exact hk s
  have h1 : ((1 : O) ⊗ₜ[ℤ_[l]] u) ^ s * ((l : OB l O) ^ s * x) = x := by
    have h2 : ((1 : O) ⊗ₜ[ℤ_[l]] u) * (l : OB l O) = 1 := by
      rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] (l : Per.Bcris l) from
        (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, hu]
      rfl
    rw [← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
  rw [← h1]
  simpa using mul_mem_filO hU h

theorem j_mem_FilP_of_approx (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ y z : Per.Acris l, x = y + (l : Per.Acris l) ^ r * z ∧ C.j y ∈ Per.FilP l m) :
    C.j x ∈ Per.FilP l m := by
  obtain ⟨N, hN⟩ := C.j_cris.bdd m
  obtain ⟨a, ha⟩ := hN x
  have hq : Ideal.Quotient.mk (Per.kerP l ^ m) (algebraMap (Per.Ainf l) (Per.AinfP l) a) = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    obtain ⟨b, hb⟩ := hN z
    refine ⟨b, ?_⟩
    have hy' : Per.ev l m (C.j y) = 0 := (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).1 hy
    rw [← ha, ← hb, hxyz]
    simp only [map_add, map_mul, map_pow, map_natCast, hy']
    ring
  have h1 : Per.ev l m (C.j x) = 0 := by
    rw [← ha, map_mul, map_pow, map_natCast] at hq
    exact ((GlobalTheory.MemLoc.CrisMap.unit_l l m).pow N).mul_right_eq_zero.1 hq
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m _).2 h1

end GlobalTheory.BKGal.TaylorFil
