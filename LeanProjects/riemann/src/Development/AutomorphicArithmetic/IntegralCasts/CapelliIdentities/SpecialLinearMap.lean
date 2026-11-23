import Mathlib

private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    (v : I) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W v) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x v y j)
      = ∏ j ∈ Finset.univ.erase v, a j (x j) :=
  Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne {I : Type} [Fintype I] [DecidableEq I]
    {W : I → Type} [(i : I) → AddCommGroup (W i)] [(i : I) → _root_.Module ℂ (W i)]
    {v i : I} (h : i ≠ v) (a : (i : I) → Module.Dual ℂ (W i)) (x : (i : I) → W i) (y : W i) :
    ∏ j ∈ Finset.univ.erase v, a j (Function.update x i y j)
      = a i y * ∏ j ∈ (Finset.univ.erase v).erase i, a j (x j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
    Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

noncomputable def UpperTheory.Reformulated.B.SpecialLinearMap.slM :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → MultilinearMap ℂ W (W v) :=
  fun {I} _ dI {_} _ _ v a =>
    { toFun := fun x => (∏ j ∈ Finset.univ.erase v, a j (x j)) • x v
      map_update_add' := fun {d} x i y z => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self, smul_add]
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_add, add_mul, add_smul]
      map_update_smul' := fun {d} x i c y => by
        obtain rfl : d = dI := Subsingleton.elim _ _
        by_cases h : i = v
        · subst h
          simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_self, Function.update_self]
          exact smul_comm _ _ _
        · simp only [UpperTheory.Reformulated.B.SpecialLinearMap.prod_update_ne h, Function.update_of_ne (Ne.symm h),
            map_smul, smul_eq_mul, mul_assoc, mul_smul] }
