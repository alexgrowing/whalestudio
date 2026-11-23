import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil

variable {l : ℕ} [Fact l.Prime]

theorem mem_FilD_zero_iff (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ z : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) z := by
  have h := GlobalTheory.BdRQuot.mem_FilD_nat (l := l) 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, GlobalTheory.BdRQuot.mem_filtration_zero z, rfl⟩

theorem mul_mem_FilD_of_zero {x y : Per.BdR l} {n : ℤ} (hx : x ∈ Per.FilD l 0) (hy : y ∈ Per.FilD l n) :
    x * y ∈ Per.FilD l n := by
  obtain ⟨z, rfl⟩ := (mem_FilD_zero_iff x).1 hx
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ z hy

theorem mul_mem_FilD_neg {x y : Per.BdR l} {m : ℕ} (hx : x ∈ Per.FilD l m) (hy : y ∈ Per.FilD l (-(m : ℤ))) :
    x * y ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.BdRField.exists_isEps l
  obtain ⟨w, rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ x).1 hx
  obtain ⟨w', rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ y).1 hy
  rw [mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul,
    ← map_mul]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def filO (C : GlobalTheory.MemLoc.Core l) (n : ℤ) : Submodule O (OB l O) :=
  Submodule.span O {x | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l n ∧ x = (1 : O) ⊗ₜ[ℤ_[l]] β}

variable {O} {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

def filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) (n : ℤ) : Submodule O (TW (OB l O) T) :=
  Submodule.span O {w | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l n ∧
    w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}

theorem smul_mem_filT {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {a b c : ℤ}
    (hmul : ∀ β β' : Per.Bcris l, C.ι β ∈ Per.FilD l a → C.ι β' ∈ Per.FilD l b → C.ι (β * β') ∈ Per.FilD l c)
    {r : OB l O} (hr : r ∈ filO O C a) {v : TW (OB l O) T} (hv : v ∈ filT C T b) : r • v ∈ filT C T c := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨β, hβ, rfl⟩ := hr
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β', x, hβ', rfl⟩ := hv
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact Submodule.subset_span ⟨β * β', x, hmul β β' hβ hβ', rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul o v _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_smul]; exact zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | smul o r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ o h

theorem smul_mem_filT_of_zero {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {n : ℤ} {r : OB l O}
    (hr : r ∈ filO O C 0) {v : TW (OB l O) T} (hv : v ∈ filT C T n) : r • v ∈ filT C T n :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_of_zero h h') hr hv

theorem smul_mem_filT_neg {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {m : ℕ} {r : OB l O}
    (hr : r ∈ filO O C m) {v : TW (OB l O) T} (hv : v ∈ filT C T (-(m : ℤ))) : r • v ∈ filT C T 0 :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_neg h h') hr hv

end GlobalTheory.BKGal.XiFil
