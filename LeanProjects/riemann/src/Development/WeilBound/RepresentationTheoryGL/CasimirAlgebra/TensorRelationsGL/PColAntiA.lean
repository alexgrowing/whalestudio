import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiB

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}

theorem deg_mono {d : ℕ} {g : Module.End ℂ (TV n M (Fin m))} (h : Deg E d g) :
    ∀ d', d ≤ d' → Deg E d' g := by
  induction h with
  | one d => intro d' _; exact Deg.one d'
  | add _ _ ih1 ih2 => intro d' h; exact Deg.add (ih1 d' h) (ih2 d' h)
  | smul c _ ih => intro d' h; exact Deg.smul c (ih d' h)
  | @om d g p _ ih =>
    intro d' h
    obtain ⟨k, rfl⟩ : ∃ k, d' = k + 1 := ⟨d' - 1, by omega⟩
    exact Deg.om p (ih k (by omega))
  | perm σ _ ih => intro d' h; exact Deg.perm σ (ih d' h)

theorem deg_mul {d d' : ℕ} {g h : Module.End ℂ (TV n M (Fin m))} (hg : Deg E d g) (hh : Deg E d' h) :
    Deg E (d + d') (g * h) := by
  induction hh with
  | one d' => rw [mul_one]; exact deg_mono hg _ (by omega)
  | add _ _ ih1 ih2 => rw [mul_add]; exact Deg.add ih1 ih2
  | smul c _ ih => rw [mul_smul_comm]; exact Deg.smul c ih
  | om p _ ih => rw [← mul_assoc]; exact Deg.om p ih
  | perm σ _ ih => rw [← mul_assoc]; exact Deg.perm σ ih

theorem deg_zero (d : ℕ) : Deg E d (0 : Module.End ℂ (TV n M (Fin m))) := by
  have := Deg.smul (E := E) (0 : ℂ) (Deg.one (P := Fin m) d)
  rwa [zero_smul] at this

theorem deg_sum {d : ℕ} (s : Finset (Fin m)) (f : Fin m → Module.End ℂ (TV n M (Fin m)))
    (hf : ∀ i ∈ s, Deg E d (f i)) : Deg E d (∑ i ∈ s, f i) := by
  classical
  exact Finset.sum_induction f (Deg E d) (fun _ _ ha hb => Deg.add ha hb) (deg_zero d) hf

theorem deg_xJ (j : Fin m) : Deg E 1 (xJ E j) := by
  unfold xJ
  refine Deg.add ?_ (deg_sum _ _ fun i _ => ?_)
  · have := Deg.om (E := E) j (Deg.one (P := Fin m) 0)
    rwa [one_mul] at this
  · have := Deg.perm (E := E) (Equiv.swap i j) (Deg.one (P := Fin m) 1)
    rwa [one_mul] at this

theorem deg_factor (i j : Fin m) (c : Prop) [Decidable c] :
    Deg E (if c then 1 else 0) (if c then xJ E i - xJ E j + 1 else 1) := by
  split_ifs
  · refine Deg.add ?_ (Deg.one 1)
    rw [sub_eq_add_neg]
    refine Deg.add (deg_xJ i) ?_
    have h1 := Deg.smul (-1 : ℂ) (deg_xJ (E := E) j)
    rwa [neg_one_smul] at h1
  · exact Deg.one 0

theorem deg_prod : ∀ (k : ℕ) (f : Fin k → Module.End ℂ (TV n M (Fin m))) (e : Fin k → ℕ),
    (∀ i, Deg E (e i) (f i)) → Deg E (∑ i, e i) (List.ofFn f).prod := by
  intro k
  induction k with
  | zero => intro f e _; simpa using Deg.one (E := E) (P := Fin m) 0
  | succ k ih =>
    intro f e hf
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact deg_mul (hf 0) (ih _ _ fun i => hf i.succ)

theorem npairs_eq (col : Fin m → ℕ) :
    (∑ j : Fin m, ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0) = npairs col := by
  unfold npairs
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]

theorem deg_colD {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) :
    Deg E (npairs col) (colD E col : Module.End ℂ (TV n M (Fin m))) := by
  have h := deg_prod m
    (fun j => (List.ofFn fun i : Fin m => if i < j ∧ col i = col j then xJ E i - xJ E j + 1 else 1).prod)
    (fun j => ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0)
    (fun j => deg_prod m _ _ (fun i => deg_factor i j _))
  rw [npairs_eq] at h
  exact h

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
