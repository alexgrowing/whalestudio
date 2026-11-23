import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k (n := n) d j i) = 0 := by
  simp [pt]

theorem cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by
  simp

theorem CZ.nil {n : ℕ} : CZ (![] : Fin 0 → Pt k n d) := by
  intro j
  exact j.elim0

theorem CZ.cons {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j
  cases j using Fin.cases with
  | zero => simpa using hp
  | succ j => simpa using ha j

theorem pt_apply {n : ℕ} (j : Fin n) (i : Fin d) : pt k (n := n) d j i = (X (j, i) : PS k n d) := rfl

variable (G : FGLaw k d)

theorem cz_F : ∀ i, constantCoeff (G.F i) = 0 := G.const

theorem formalGroupLaw_ev_x_zero (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have ha : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil)
  have hb : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) :=
    CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)
  rw [← G.comm i, ev_ev ha hb]
  have e : (fun j l => ev (n := 1) (![pt k d 0, 0] : Fin 2 → Pt k 1 d)
      ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j l)) = (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X ha]
  rw [e]
  exact G.unit i

theorem pderiv_ev_zero {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d)
    (h : ∀ j i, pderiv k v (a j i) = 0) : pderiv k v (ev a f) = 0 := by
  rw [pderiv_ev ha]
  exact Finset.sum_eq_zero (fun p _ => by rw [h p.1 p.2, mul_zero])

theorem pderiv_pt {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv k v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  first
  | rw [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]
  | (rw [pt_apply, MvPowerSeries.pderiv_X]; simp [Pi.single_apply])

def Jac : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))

def Ar : Fin d → Fin d → PS k 2 d := fun i b => pderiv k ((1 : Fin 2), b) (G.F i)

section Fams

theorem cz1 : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil)
theorem czY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt _) CZ.nil
theorem czZ : CZ (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) :=
  CZ.cons (cc_pt _) (CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil))
theorem czFF : CZ (![G.F] : Fin 1 → Pt k 2 d) := CZ.cons (cz_F G) CZ.nil
theorem cz01 : CZ (![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)
theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)

end Fams

private theorem ev_zero_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simpa using ev_sub ha (0 : PS k m d) 0

theorem formal_ev_second_point_of_x_zero (g : PS k 2 d) :
    ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czY cz1]
  congr 1
  funext j l
  fin_cases j
  · simp [pt_apply, ev_X czY]
  · simp [ev_zero_of_CZ czY]

theorem ev_z_yz (g : PS k 2 d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czZ cz12]
  congr 1
  funext j l
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem formalGroupLaw_ev_y_zero (c : Fin d) : ev (n := 2) ![pt k d 1, 0] (G.F c) = (X ((1 : Fin 2), c) : PS k 2 d) := by
  rw [← formal_ev_second_point_of_x_zero, formalGroupLaw_ev_x_zero, ev_X czY]
  simp [pt_apply]

private theorem ev_two_identity (f : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
  have h : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k d j := by
    funext j
    fin_cases j <;> rfl
  rw [h, ev_pt]

private theorem ev_finset_sum_of_CZ {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : Fin d → PS k m d) :
    ev a (∑ c, f c) = ∑ c, ev a (f c) :=
  map_sum (AddMonoidHom.mk' (ev a) (ev_add ha)) f Finset.univ

private theorem ev_zero_one_identity (g : PS k 2 d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) (ev (n := 3) ![pt k d 0, pt k d 1] g) = g := by
  rw [ev_ev czZ cz01]
  have e : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j l)) = (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  rw [e, ev_two_identity]

private theorem pderiv_two_ev (b : Fin d) (g : PS k 2 d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] g) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) g) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]

private theorem ev_jacobian_left (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv k ((2 : Fin 3), b)
        (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i))) =
      ev (n := 2) ![G.F] (Jac G i b) := by
  have hA : CZ (![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (fun l => constantCoeff_ev cz01 (cz_F G l)) (CZ.cons (cc_pt _) CZ.nil)
  have h0 : ∀ l, pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] (G.F l)) = 0 := fun l =>
    pderiv_ev_zero cz01 _ _ (fun j i => by fin_cases j <;> simp [pderiv_pt])
  have hs : pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] (G.F i)) =
      ev (n := 3) ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2]
        (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [pderiv_ev hA, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [h0, pderiv_pt]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] : Fin 2 → Pt k 3 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [ev_zero_one_identity]
    · simp [pt_apply, ev_X czZ]
  have e2 : (fun j l => ev (n := 2) (![G.F] : Fin 1 → Pt k 2 d) ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j l)) =
      (![G.F, 0] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X (czFF G)]
    · simp [ev_zero_of_CZ (czFF G)]
  rw [hs, ev_ev czZ hA, e1]
  simp only [Jac]
  rw [ev_ev (czFF G) cz1, e2]

private theorem ev_jacobian_right (i b : Fin d) :
    ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      (pderiv k ((2 : Fin 3), b)
        (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i))) =
      ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  have hB : CZ (![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt _) (CZ.cons (fun l => constantCoeff_ev cz12 (cz_F G l)) CZ.nil)
  have hs : pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] (G.F i)) =
      ∑ c, ev (n := 3) ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)]
          (pderiv k ((1 : Fin 2), c) (G.F i)) *
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := by
    rw [pderiv_ev hB, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [pderiv_pt, pderiv_two_ev]
  have e1 : (fun j l => ev (n := 2) (![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d)
      ((![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] : Fin 2 → Pt k 3 d) j l)) =
      (![pt k d 0, pt k d 1] : Fin 2 → Pt k 2 d) := by
    funext j l
    fin_cases j
    · simp [pt_apply, ev_X czZ]
    · simp [ev_z_yz, formalGroupLaw_ev_y_zero, pt_apply]
  rw [hs, ev_finset_sum_of_CZ czZ]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [ev_mul czZ, ev_ev czZ hB, e1, ev_two_identity, ev_z_yz]
  simp only [Ar, Jac, formal_ev_second_point_of_x_zero]

theorem jac_F (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  rw [← ev_jacobian_left, ← ev_jacobian_right, G.assoc i]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
