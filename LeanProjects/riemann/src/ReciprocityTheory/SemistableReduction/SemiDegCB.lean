import ReciprocityTheory.SemistableReduction.SemiDegCA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

def consZero (K : Type) [Field K] (k : ℕ) : (Fin k → K) →ₗ[K] (Fin (k + 1) → K) where
  toFun y := Fin.cons 0 y
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem consZero_zero (K : Type) [Field K] {k : ℕ} (y : Fin k → K) :
    consZero K k y 0 = 0 := rfl

@[simp] theorem consZero_succ (K : Type) [Field K] {k : ℕ} (y : Fin k → K) (i : Fin k) :
    consZero K k y i.succ = y i := rfl

theorem consZero_injective (K : Type) [Field K] (k : ℕ) : Function.Injective (consZero K k) := by
  intro x y h
  funext i
  simpa using congrFun h i.succ

theorem consZero_tail (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hx]
  · simp [Fin.tail]

theorem single_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} (i : Fin k) {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : Pi.single i a ∈ intVec K k := by
  classical
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  intro j
  by_cases h : j = i
  · subst h
    simpa using ha
  · simp [Pi.single_apply, h, Submodule.zero_mem]

theorem consZero_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h i
    simpa using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Submodule.zero_mem]
    · simpa using h j

theorem lattice_split (K : Type) [Field K] [NumberField K] : ∀ (k : ℕ)
    (X : Submodule (𝓞 K) (Fin k → K)), X.FG → intVec K k ≤ X →
    ∃ (C : Fin k → Submodule (𝓞 K) K) (z : Fin k → Fin k → K),
      (∀ i, (C i).FG) ∧ (∀ i, 1 ≤ C i) ∧ (∀ j i : Fin k, i < j → z j i = 0) ∧
      (∀ j, z j j = 1) ∧
      (∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) ∧
      (∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i) ∧
      (intVec K k).toAddSubgroup.relIndex X.toAddSubgroup =
        ∏ i, (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (C i).toAddSubgroup
  | 0, X, _, _ => by
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => j.elim0,
      fun j => j.elim0, fun t _ => ?_, fun x _ => ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
    · convert X.zero_mem using 1
    · ext i
      exact i.elim0
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [AddSubgroup.relIndex_eq_one]
      intro x _
      rw [Submodule.mem_toAddSubgroup, mem_intVec]
      intro i
      exact i.elim0
  | k + 1, X, hfg, hstd => by
    let p0 : (Fin (k + 1) → K) →ₗ[K] K := LinearMap.proj 0
    set C0 := X.map (p0.restrictScalars (𝓞 K)) with hC0
    have hC0fg : C0.FG := hfg.map _
    have hC01 : 1 ≤ C0 := by
      intro a ha
      exact Submodule.mem_map.2 ⟨Pi.single 0 a, hstd (single_mem_intVec K 0 ha), by simp [p0]⟩
    obtain ⟨v, hv1, hv⟩ := exists_section_of_image X p0 hC0fg hC01
    let cz := (consZero K k).restrictScalars (𝓞 K)
    let X' : Submodule (𝓞 K) (Fin k → K) := X.comap cz
    have hX'fg : X'.FG := by
      apply Submodule.fg_of_fg_map_injective cz (consZero_injective K k)
      have : IsNoetherian (𝓞 K) X := isNoetherian_of_fg_of_noetherian X hfg
      exact Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _)
    have hstd' : intVec K k ≤ X' := fun y hy =>
      hstd ((consZero_mem_intVec K).2 hy)
    obtain ⟨C', z', hfg', h1', htri', hdiag', hin', hdec', hidx'⟩ :=
      lattice_split K k X' hX'fg hstd'
    let C : Fin (k + 1) → Submodule (𝓞 K) K := Fin.cons C0 C'
    let z : Fin (k + 1) → Fin (k + 1) → K := Fin.cons v fun j => consZero K k (z' j)
    have hsum : ∀ t : Fin (k + 1) → K,
        ∑ i, t i • z i = t 0 • v + consZero K k (∑ j, t j.succ • z' j) := by
      intro t
      rw [Fin.sum_univ_succ, map_sum]
      simp [z, map_smul]
    refine ⟨C, z, fun i => Fin.cases hC0fg hfg' i, fun i => Fin.cases hC01 h1' i, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i hij
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero i)
      | succ j =>
        induction i using Fin.cases with
        | zero => rfl
        | succ i => exact htri' j i (Fin.succ_lt_succ_iff.1 hij)
    · intro j
      induction j using Fin.cases with
      | zero => exact hv1
      | succ j => exact hdiag' j
    · intro t ht
      rw [hsum]
      refine X.add_mem (hv _ (ht 0)) ?_
      exact hin' (fun j => t j.succ) (fun j => ht j.succ)
    · intro x hx
      have ht0 : x 0 ∈ C0 := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      set y := x - x 0 • v with hy
      have hyX : y ∈ X := X.sub_mem hx (hv _ ht0)
      have hy0 : y 0 = 0 := by
        have : p0 v = v 0 := rfl
        simp [hy, ← this, hv1]
      have hyX' : Fin.tail y ∈ X' := by
        show cz (Fin.tail y) ∈ X
        exact (consZero_tail K y hy0).symm ▸ hyX
      obtain ⟨t', ht', hyt⟩ := hdec' _ hyX'
      refine ⟨Fin.cons (x 0) t', fun i => Fin.cases ht0 ht' i, ?_⟩
      rw [hsum]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hyt, consZero_tail K y hy0, hy]
      abel
    · have hA : (intVec K (k + 1)).toAddSubgroup.map p0.toAddMonoidHom =
          (1 : Submodule (𝓞 K) K).toAddSubgroup := by
        ext a
        simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact mem_intVec.1 hx 0
        · intro ha
          exact ⟨Pi.single 0 a, single_mem_intVec K 0 ha, by simp [p0]⟩
      have hB : X.toAddSubgroup.map p0.toAddMonoidHom = C0.toAddSubgroup := by
        ext a
        simp [C0, Submodule.mem_map]
      have hAk : (intVec K (k + 1)).toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          (intVec K k).toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          rw [← consZero_mem_intVec K, consZero_tail K x h0]
          exact hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨(consZero_mem_intVec K).2 hy, rfl⟩
      have hBk : X.toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          X'.toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          show cz (Fin.tail x) ∈ X
          exact (consZero_tail K x h0).symm ▸ hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hy, rfl⟩
      rw [relIndex_eq_map_mul_ker p0.toAddMonoidHom
          ((Submodule.toAddSubgroup_le _ _).2 hstd), hA, hB, hAk, hBk,
        AddSubgroup.relIndex_map_map_of_injective _ _ (consZero_injective K k), hidx',
        Fin.prod_univ_succ]
      rfl

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
