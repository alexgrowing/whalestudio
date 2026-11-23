import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]
  simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add, map_add]; exact add_mem (h i) (h' i)
  | smul o w _ h =>
    rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1
  rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
