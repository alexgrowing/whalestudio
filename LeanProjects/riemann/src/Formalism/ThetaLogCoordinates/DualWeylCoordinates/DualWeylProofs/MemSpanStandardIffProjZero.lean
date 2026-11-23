import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_ev_zero_of_mem {M : GLMod n} (CF : ColFam M) (F : Type) [CommRing F] {pi : Set (Fin n → ℤ)}
    (hpi : DomLowerSet pi) {j : CF.J} (hj : CF.mu j ∈ pi) (I : TIdx (CF.mu j)) {mu : Fin n → ℤ}
    (hmu : Dominant mu) (hout : mu ∉ pi) : qb_ev M F mu (fun i => (CF.vec j I i : F)) = 0 :=
  qb_key_zero CF F j I mu fun hle => hout (hpi.2 _ hj _ hmu hle)

lemma qb_exists_coeff (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : M.ι → R) :
    ∃ a : qb_Idx CF → R, x = ∑ y, a y • qb_vecF CF R y := by
  refine ⟨fun y => (qb_basis hA CF R).repr x y, ?_⟩
  conv_lhs => rw [← (qb_basis hA CF R).sum_repr x]
  simp only [qb_basis_apply]

theorem mem_span_standard_iff_proj_zero (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (F : Type) [Field F] (x : M.ι → F) :
    x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu x = 0 := by
  constructor
  · intro hx mu hmu hout
    have : Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧
        y = fun i => (CF.vec j I i : F)} ≤ LinearMap.ker (qb_evL M F mu) := by
      rw [Submodule.span_le]
      rintro y ⟨j, hj, I, -, rfl⟩
      exact qb_ev_zero_of_mem CF F hpi hj I hmu hout
    exact this hx
  · intro h
    obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF F x
    have hs := qb_supp_in hA CF F a pi hpi h
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : a y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y.1, hs y hy, y.2.1, y.2.2, rfl⟩)

theorem qb_mem_std (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (x : M.ι → ℤ) (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M ℚ mu (fun i => (x i : ℚ)) = 0) :
    x ∈ Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF ℤ x
  have hc : (fun i => (((∑ y, a y • qb_vecF CF ℤ y) i : ℤ) : ℚ)) = ∑ y, (a y : ℚ) • qb_vecF CF ℚ y := by
    funext i
    simp [qb_vecF, Finset.sum_apply]
  rw [hc] at h
  have hs := qb_supp_in hA CF ℚ (fun y => (a y : ℚ)) pi hpi h
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, y.2.2, by rw [qb_vecF_int]⟩)

theorem qb_Mpi_eq (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  apply le_antisymm
  · unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro x ⟨j, hj, I, rfl⟩
    exact qb_mem_std hA CF pi hpi _ fun mu hmu hout => qb_ev_zero_of_mem CF ℚ hpi hj I hmu hout
  · apply Submodule.span_mono
    rintro x ⟨j, hj, I, -, rfl⟩
    exact ⟨j, hj, I, rfl⟩

theorem qb_Mpi_eq_image (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}) := by
  rw [qb_Mpi_eq hA CF pi hpi]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, I, hI, rfl⟩
    exact ⟨⟨j, I, hI⟩, hj, by rw [qb_basis_apply, qb_vecF_int]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, y.2.1, y.2.2, by rw [qb_basis_apply, qb_vecF_int]⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
