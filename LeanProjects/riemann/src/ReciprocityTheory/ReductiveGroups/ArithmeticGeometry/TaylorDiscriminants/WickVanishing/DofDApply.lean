import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

variable {k : Type} [CommRing k] {d : ℕ}

def dofCoef (F : Fin d → PS k 2 d) (v : Fin d → k) (j : Fin d) : PS k 1 d :=
  ∑ i : Fin d, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (F j))

def dofD (F : Fin d → PS k 2 d) (v : Fin d → k) : Derivation k (PS k 1 d) (PS k 1 d) :=
  ∑ j : Fin d, dofCoef F v j • pderiv k ((0 : Fin 1), j)

theorem dofD_apply (F : Fin d → PS k 2 d) (v : Fin d → k) (f : PS k 1 d) :
    dofD F v f = Dof F v f := by
  have h : ∀ (s : Finset (Fin d)) (D : Fin d → Derivation k (PS k 1 d) (PS k 1 d)),
      (∑ j ∈ s, D j) f = ∑ j ∈ s, D j f := by
    intro s D
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  rw [dofD, h]
  simp only [Derivation.smul_apply, smul_eq_mul, Dof, dofCoef]

theorem dof_add (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  simp only [← dofD_apply, map_add]

theorem dof_zero (F : Fin d → PS k 2 d) (v : Fin d → k) : Dof F v 0 = 0 := by
  simp only [← dofD_apply, map_zero]

theorem dof_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f * g) = f * Dof F v g + g * Dof F v f := by
  simp only [← dofD_apply, Derivation.leibniz, smul_eq_mul]

theorem dof_C (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) : Dof F v (C r) = 0 := by
  have hC : (C r : PS k 1 d) = r • (1 : PS k 1 d) := by
    rw [MvPowerSeries.smul_eq_C_mul, mul_one]
  rw [← dofD_apply, hC, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

theorem dof_C_mul (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  rw [dof_mul, dof_C, mul_zero, add_zero]

theorem dof_sum (F : Fin d → PS k 2 d) (v : Fin d → k) {α : Type} (s : Finset α) (f : α → PS k 1 d) :
    Dof F v (∑ a ∈ s, f a) = ∑ a ∈ s, Dof F v (f a) := by
  simp only [← dofD_apply, map_sum]

end ReciprocityTheory.ChartRestriction.G.TB.GE
