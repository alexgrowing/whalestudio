import Mathlib

theorem UpperTheory.Reformulated.B.Qk12.list_eig :
    ∀ {M ι : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι),
    (∀ i ∈ l, (L i : M → M) x = c i • x) → ((List.map L l).prod : M → M) x = (List.map c l).prod • x := by
  intro M ι _ _ L c x l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have h1 : L a x = c a • x := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, h2,
      map_smul, h1, smul_smul, mul_comm]
