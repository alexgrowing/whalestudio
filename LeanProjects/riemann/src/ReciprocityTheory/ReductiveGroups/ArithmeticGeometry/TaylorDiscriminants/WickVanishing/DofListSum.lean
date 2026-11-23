import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Dof
variable (F : Fin d → PS k 2 d) (v : Fin d → k)

theorem dof_add (f g : PS k 1 d) : Dof F v (f + g) = Dof F v f + Dof F v g := by
  unfold Dof
  simp only [map_add, mul_add, Finset.sum_add_distrib]

theorem dof_zero : Dof F v (0 : PS k 1 d) = 0 := by
  simp [Dof]

theorem dof_C (a : k) : Dof F v (C a : PS k 1 d) = 0 := by
  unfold Dof
  have h : ∀ j : Fin d, pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0 := fun j => by
    simp
  simp [h]

theorem dof_mul (f g : PS k 1 d) : Dof F v (f * g) = Dof F v f * g + f * Dof F v g := by
  unfold Dof
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem dof_list_sum (L : List (PS k 1 d)) : Dof F v L.sum = (L.map (Dof F v)).sum := by
  induction L with
  | nil => simp [dof_zero]
  | cons a L ih => simp [dof_add, ih]

end Dof

section Words
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

def T (w : List ι) (A : PS k 1 d) : PS k 1 d := w.foldr (fun l g => Dof F (u l) g) A

theorem T_cons (l : ι) (w : List ι) (A : PS k 1 d) : T F u (l :: w) A = Dof F (u l) (T F u w A) := rfl

theorem T_append (w w' : List ι) (A : PS k 1 d) : T F u (w ++ w') A = T F u w (T F u w' A) := by
  simp [T, List.foldr_append]

theorem T_add (w : List ι) (A B : PS k 1 d) : T F u w (A + B) = T F u w A + T F u w B := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [T_cons, T_cons, T_cons, ih, dof_add]

theorem T_zero (w : List ι) : T F u w (0 : PS k 1 d) = 0 := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [T_cons, ih, dof_zero]

def splits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | l :: w => (splits w).map (fun p => (l :: p.1, p.2)) ++ (splits w).map (fun p => (p.1, l :: p.2))

theorem T_mul (w : List ι) (A B : PS k 1 d) :
    T F u w (A * B) = ((splits w).map (fun p => T F u p.1 A * T F u p.2 B)).sum := by
  induction w with
  | nil => simp [splits, T]
  | cons l w ih =>
    rw [T_cons, ih, dof_list_sum, List.map_map]
    simp only [splits, List.map_append, List.map_map, List.sum_append]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [dof_mul]
    rfl

end Words

end ReciprocityTheory.ChartRestriction.G.TB.G2
