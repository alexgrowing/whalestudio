import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

section Ring

variable {R : Type} [CommRing R] {m : ℕ}

theorem mul_apply_super {u c : GL (Fin m) R} (hu : u ∈ unipB R (Fin m)) (hc : c ∈ unipB R (Fin m))
    {i j : Fin m} (hij : j.val = i.val + 1) :
    ((u * c : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j =
      (u : Matrix (Fin m) (Fin m) R) i j + (c : Matrix (Fin m) (Fin m) R) i j := by
  obtain ⟨hu0, hu1⟩ := (mem_unipB _).1 hu
  obtain ⟨hc0, hc1⟩ := (mem_unipB _).1 hc
  have hne : i ≠ j := by intro h; subst h; omega
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add i j hne]
  · rw [hu1, hc1, one_mul, mul_one, add_comm]
  · rintro l ⟨hli, hlj⟩
    rcases lt_or_gt_of_ne hli with h | h
    · rw [hu0 i l h, zero_mul]
    · have hjl : j < l := by
        have h1 := Fin.val_ne_of_ne hlj
        rw [Fin.lt_def] at h ⊢
        omega
      rw [hc0 l j hjl, mul_zero]

theorem superDiag_mul {u c : GL (Fin m) R} (hu : u ∈ unipB R (Fin m)) (hc : c ∈ unipB R (Fin m)) :
    superDiag (u * c) = superDiag u + superDiag c := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  exact mul_apply_super hu hc (Finset.mem_filter.1 hj).2

theorem wRev_sq : (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id * (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id
    = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev i)]
  · simp [Matrix.one_apply]
  · intro l hl
    simp [Matrix.one_apply, Ne.symm hl]

def wRev (R : Type) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  ⟨(1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id, (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id,
    wRev_sq, wRev_sq⟩

theorem wRev_mul_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((wRev R m * M : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j = (M : Matrix (Fin m) (Fin m) R) (Fin.rev i) j := by
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev i)]
  · show (1 : Matrix (Fin m) (Fin m) R) (Fin.rev i) (Fin.rev i) * _ = _
    rw [Matrix.one_apply_eq, one_mul]
  · intro l hl
    simp [wRev, Ne.symm hl]

theorem mul_wRev_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((M * wRev R m : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j = (M : Matrix (Fin m) (Fin m) R) i (Fin.rev j) := by
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev j)]
  · show _ * (1 : Matrix (Fin m) (Fin m) R) (Fin.rev (Fin.rev j)) j = _
    rw [Fin.rev_rev, Matrix.one_apply_eq, mul_one]
  · intro l hl
    have : Fin.rev l ≠ j := fun h => hl (by rw [← h, Fin.rev_rev])
    simp [wRev, this]

theorem wRev_inv : (wRev R m)⁻¹ = wRev R m := Units.ext rfl

theorem wRev_conj_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((wRev R m * M * wRev R m : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j =
      (M : Matrix (Fin m) (Fin m) R) (Fin.rev i) (Fin.rev j) := by
  rw [mul_wRev_apply, wRev_mul_apply]

end Ring

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem det_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : (u : Matrix (Fin m) (Fin m) k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => ((mem_unipB _).1 hu).1 i j hij)]
  simp [((mem_unipB _).1 hu).2]

theorem mem_KO_of_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m))
    (h : ∀ i j, valuation k ((u : Matrix (Fin m) (Fin m) k) i j) ≤ 1) : u ∈ KO k (Fin m) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).2 (h i j), fun i j => ?_⟩
  have hinv : ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = (u : Matrix (Fin m) (Fin m) k).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, det_unip hu, Ring.inverse_one, one_smul]
  let A : Matrix (Fin m) (Fin m) 𝒪[k] := fun i j => ⟨(u : Matrix (Fin m) (Fin m) k) i j,
    (Valuation.mem_integer_iff _ _).2 (h i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (u : Matrix (Fin m) (Fin m) k) := by ext i j; rfl
  show ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j ∈ 𝒪[k]
  rw [hinv, ← hA, ← RingHom.map_adjugate]
  exact (A.adjugate i j).2

theorem mem_KOne_of_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m))
    (h : ∀ i j, i < j → valuation k ((u : Matrix (Fin m) (Fin m) k) i j) < 1) : u ∈ KOne k (Fin m) := by
  refine GlobalTheory.StepData.mem_KOne.2 fun i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hij
  · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne] using h i j hij
  · simp [Matrix.sub_apply, ((mem_unipB _).1 hu).2 i]
  · simp [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', ((mem_unipB _).1 hu).1 i j hij]

theorem val_lt_of_mem_KOne {u : GL (Fin m) k} (hu : u ∈ KOne k (Fin m)) {i j : Fin m} (hij : i ≠ j) :
    valuation k ((u : Matrix (Fin m) (Fin m) k) i j) < 1 := by
  have := GlobalTheory.StepData.mem_KOne.1 hu i j
  simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using this

theorem val_le_of_mem_KO {u : GL (Fin m) k} (hu : u ∈ KO k (Fin m)) (i j : Fin m) :
    valuation k ((u : Matrix (Fin m) (Fin m) k) i j) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff u).1 hu).1 i j)

end Local

end DiscreteGroups.sglob.DzType
