import Mathlib

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.relWeight :
    ∀ (A : Type) [CommGroup A] (ι : Type) [Fintype ι] (a : ι → A), (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      ∃ w : ι → ℤ, Function.Injective w ∧ ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0 := by
  intro A _ ι _ a ha
  classical
  obtain ⟨P, hP⟩ : ∃ P : (ι → ℤ) → A, ∀ m, P m = ∏ i, a i ^ m i := ⟨_, fun _ => rfl⟩
  have hPadd : ∀ m n, P (m + n) = P m * P n := by
    intro m n
    rw [hP, hP, hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, _root_.zpow_add]
  have hPsmul : ∀ (c : ℤ) m, P (c • m) = P m ^ c := by
    intro c m
    rw [hP, hP, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, _root_.zpow_mul]
  have hPsub : ∀ m n, P (m - n) = P m / P n := by
    intro m n
    rw [eq_div_iff_mul_eq', ← hPadd, sub_add_cancel]
  have hPe : ∀ i, P (Pi.single i 1) = a i := by
    intro i
    rw [hP]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  let L : Submodule ℤ (ι → ℤ) :=
    { carrier := {m | ∃ k : ℤ, k ≠ 0 ∧ P (k • m) = 1}
      add_mem' := by
        rintro m n ⟨k, hk, hm⟩ ⟨l, hl, hn⟩
        refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
        have e1 : P ((k * l) • m) = 1 := by rw [mul_comm, mul_smul, hPsmul, hm, _root_.one_zpow]
        have e2 : P ((k * l) • n) = 1 := by rw [mul_smul, hPsmul, hn, _root_.one_zpow]
        rw [smul_add, hPadd, e1, e2, one_mul]
      zero_mem' := ⟨1, one_ne_zero, by simp [hP]⟩
      smul_mem' := by
        rintro c m ⟨k, hk, hm⟩
        exact ⟨k, hk, by rw [smul_comm, hPsmul, hm, _root_.one_zpow]⟩ }
  haveI : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective L x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk, h⟩ := hx
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact h⟩
  let q : ι → (ι → ℤ) ⧸ L := fun i => L.mkQ (Pi.single i 1)
  have hq : ∀ i j, i ≠ j → q i - q j ≠ 0 := by
    intro i j hij h
    rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨k, hk, hk1⟩ := h
    apply ha i j hij
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨k, hk, ?_⟩
    rw [hPsmul, hPsub, hPe, hPe] at hk1
    exact hk1
  have hex : ∃ f : Module.Dual ℤ ((ι → ℤ) ⧸ L), ∀ i j, i ≠ j → f (q i) ≠ f (q j) := by
    by_contra hno
    push_neg at hno
    let s : Finset (ι × ι) := Finset.univ.filter fun x => x.1 ≠ x.2
    let p : ι × ι → Submodule ℤ (Module.Dual ℤ ((ι → ℤ) ⧸ L)) :=
      fun x => LinearMap.ker (Module.Dual.eval ℤ _ (q x.1 - q x.2))
    have hc : ⋃ x ∈ s, (p x : Set (Module.Dual ℤ ((ι → ℤ) ⧸ L))) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      obtain ⟨i, j, hij, h⟩ := hno f
      simp only [Set.mem_iUnion]
      refine ⟨(i, j), by simp [s, hij], ?_⟩
      simp [p, h]
    obtain ⟨⟨i, j⟩, hx, hfi⟩ := Submodule.exists_finiteIndex_of_cover hc
    have hij : i ≠ j := by simpa [s] using hx
    apply hq i j hij
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro f
    have h1 := AddSubgroup.nsmul_index_mem (p (i, j)).toAddSubgroup f
    have h2 : ((p (i, j)).toAddSubgroup.index • f) (q i - q j) = 0 := h1
    rw [LinearMap.smul_apply, smul_eq_zero] at h2
    exact h2.resolve_left hfi.index_ne_zero
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun i => f (q i), fun i j h => ?_, fun m hm => ?_⟩
  · by_contra hij
    exact hf i j hij h
  · have hm0 : L.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, one_ne_zero, by rw [one_smul, hP]; exact hm⟩
    have hsum : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h3 : ∑ i, m i • q i = 0 := by
      rw [← hm0]
      conv_rhs => rw [hsum]
      simp only [q, map_sum, LinearMap.map_smul]
    calc ∑ i, m i * f (q i) = f (∑ i, m i • q i) := by simp [map_sum]
      _ = 0 := by rw [h3, map_zero]
