import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalMulN

open GlobalTheory.GaugeAdjoint

variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)

theorem const_three {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0) (j : Fin 3)
    (i : Fin d) : constantCoeff ((![x, y, z] : Fin 3 → Pt R n d) j i) = 0 := by
  fin_cases j
  · exact hx i
  · exact hy i
  · exact hz i

theorem ev_pt_fun {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) :
    (fun i => ev a (pt R d j i)) = a j := by
  funext i
  exact ev_pt ha j i

theorem ev_zero_fun {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    (fun i => ev a ((0 : Pt R m d) i)) = 0 := by
  funext i
  exact ev_zero ha

theorem const_add {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) : constantCoeff (G.add x y i) = 0 := by
  show constantCoeff (ev ![x, y] (G.F i)) = 0
  rw [constantCoeff_ev (const_two hx hy)]
  exact G.const i

theorem ev_add_pts {x y : Pt R m d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {b : Fin m → Pt R n d}
    (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (G.add x y i)) = G.add (fun i => ev b (x i)) (fun i => ev b (y i)) := by
  funext i
  exact ev_ev_two hx hy hb (G.F i)

theorem zero_add_pt {y : Pt R n d} (hy : ∀ i, constantCoeff (y i) = 0) : G.add 0 y = y := by
  have hu : G.add 0 (pt R (n := 1) d 0) = pt R (n := 1) d 0 := funext fun i => G.unit i
  have h : (fun i => ev ![y] (G.add 0 (pt R (n := 1) d 0) i)) =
      fun i => ev ![y] (pt R (n := 1) d 0 i) := by rw [hu]
  rw [ev_add_pts G const_zero (const_pt 0) (const_one hy), ev_zero_fun (const_one hy),
    ev_pt_fun (const_one hy) 0] at h
  exact h

theorem add_comm_pt {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : G.add x y = G.add y x := by
  have hc : G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) = G.F := funext fun i => G.comm i
  have h : (fun i => ev ![x, y] (G.add (pt R (n := 2) d 1) (pt R (n := 2) d 0) i)) =
      fun i => ev ![x, y] (G.F i) := by rw [hc]
  rw [ev_add_pts G (const_pt 1) (const_pt 0) (const_two hx hy), ev_pt_fun (const_two hx hy) 1,
    ev_pt_fun (const_two hx hy) 0] at h
  exact h.symm

theorem add_zero_pt {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) : G.add x 0 = x := by
  rw [add_comm_pt G hx const_zero]
  exact zero_add_pt G hx

theorem add_assoc_pt {x y z : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have h3 := const_three hx hy hz
  have hA : G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) =
      G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) := funext fun i => G.assoc i
  have h : (fun i => ev ![x, y, z] (G.add (G.add (pt R (n := 3) d 0) (pt R d 1)) (pt R d 2) i)) =
      fun i => ev ![x, y, z] (G.add (pt R (n := 3) d 0) (G.add (pt R d 1) (pt R d 2)) i) := by
    rw [hA]
  rw [ev_add_pts G (const_add G (const_pt 0) (const_pt 1)) (const_pt 2) h3,
    ev_add_pts G (const_pt 0) (const_add G (const_pt 1) (const_pt 2)) h3,
    ev_add_pts G (const_pt 0) (const_pt 1) h3, ev_add_pts G (const_pt 1) (const_pt 2) h3,
    ev_pt_fun h3 0, ev_pt_fun h3 1, ev_pt_fun h3 2] at h
  exact h

theorem add_add_add_comm_pt {x y z w : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    G.add (G.add x y) (G.add z w) = G.add (G.add x z) (G.add y w) := by
  rw [add_assoc_pt G hx hy (const_add G hz hw), ← add_assoc_pt G hy hz hw, add_comm_pt G hy hz,
    add_assoc_pt G hz hy hw, ← add_assoc_pt G hx hz (const_add G hy hw)]

theorem const_mulN (k : ℕ) : ∀ i, constantCoeff (mulN G k i) = 0 := by
  induction k with
  | zero => intro i; exact const_zero i
  | succ k ih => intro i; exact const_add G ih (const_pt 0) i

theorem formalGroupLaw_comp_mulN_zero {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G 0) x = 0 := by
  exact ev_zero_fun (const_one hx)

theorem formalGroupLaw_comp_mulN_succ (k : ℕ) {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    comp1 (mulN G (k + 1)) x = G.add (comp1 (mulN G k) x) x := by
  show (fun i => ev ![x] (G.add (mulN G k) (pt R d 0) i)) = _
  rw [ev_add_pts G (const_mulN G k) (const_pt 0) (const_one hx), ev_pt_fun (const_one hx) 0]
  rfl

theorem formalGroupLaw_comp_mulN_add (k : ℕ) {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) :
    comp1 (mulN G k) (G.add x y) = G.add (comp1 (mulN G k) x) (comp1 (mulN G k) y) := by
  induction k with
  | zero =>
    rw [formalGroupLaw_comp_mulN_zero G (const_add G hx hy), formalGroupLaw_comp_mulN_zero G hx, formalGroupLaw_comp_mulN_zero G hy,
      zero_add_pt G const_zero]
  | succ k ih =>
    rw [formalGroupLaw_comp_mulN_succ G k (const_add G hx hy), ih, formalGroupLaw_comp_mulN_succ G k hx,
      formalGroupLaw_comp_mulN_succ G k hy,
      add_add_add_comm_pt G (const_comp1 (const_mulN G k) hx) (const_comp1 (const_mulN G k) hy) hx hy]

theorem coeff_single_one {σ : Type} (s : σ) (f : MvPowerSeries σ R) :
    coeff (Finsupp.single s 1) f = constantCoeff (pderiv R s f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem lin_ev_two {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS R 2 d) (s : Fin n × Fin d) :
    coeff (Finsupp.single s 1) (ev ![x, y] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (x l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (y l) := by
  have ha := const_two hx hy
  rw [coeff_single_one s (ev ![x, y] f), pderiv_ev ha, map_sum, Fin.sum_univ_two]
  simp only [map_sum, map_mul, constantCoeff_ev ha, ← coeff_single_one, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private lemma coeff_single_pt_eq_ite (j j' : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j', l') 1) (pt R d j l) = if j = j' ∧ l = l' then 1 else 0 := by
  show coeff _ (X (j, l)) = _
  rw [coeff_X]
  by_cases h : j = j' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := Finsupp.single_left_injective one_ne_zero h'
    simp only [Prod.mk.injEq] at h2
    exact h ⟨h2.1.symm, h2.2.symm⟩

theorem coeff_single_pt (j : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j, l') 1) (pt R d j l) = if l = l' then 1 else 0 := by
  rw [coeff_single_pt_eq_ite]
  simp

theorem lin_F_right (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  have hX : coeff (Finsupp.single ((0 : Fin 1), l) 1) (X ((0 : Fin 1), i) : PS R 1 d) =
      if i = l then 1 else 0 := coeff_single_pt 0 i l
  rw [lin_ev_two const_zero (const_pt 0), hX] at h
  simpa [coeff_single_pt] using h

private lemma coeff_single_pt_eq_ite' (j j' : Fin n) (l l' : Fin d) :
    coeff (Finsupp.single (j', l') 1) (pt R d j l) = if j = j' ∧ l = l' then 1 else 0 := by
  show coeff _ (X (j, l)) = _
  rw [coeff_X]
  by_cases h : j = j' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    have h2 := Finsupp.single_left_injective one_ne_zero h'
    simp only [Prod.mk.injEq] at h2
    exact h ⟨h2.1.symm, h2.2.symm⟩

theorem lin_F_left (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [lin_ev_two (const_pt 1) (const_pt 0)] at h
  rw [← h]
  simp [coeff_single_pt_eq_ite', lin_F_right G]

theorem dLin_add {x y : Pt R 1 d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : dLin (G.add x y) = dLin x + dLin y := by
  ext i j
  rw [Matrix.add_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![x, y] (G.F i)) =
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (x i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (y i)
  rw [lin_ev_two hx hy]
  simp [lin_F_left G, lin_F_right G]

theorem dLin_pt : dLin (pt R (n := 1) d 0) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  exact coeff_single_pt 0 i j

theorem dLin_mulN (k : ℕ) : dLin (mulN G k) = (k : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  induction k with
  | zero =>
    ext i j
    simp [dLin, mulN]
  | succ k ih =>
    show dLin (G.add (mulN G k) (pt R d 0)) = _
    rw [dLin_add G (const_mulN G k) (const_pt 0), ih, dLin_pt, Nat.cast_succ, add_smul, one_smul]

theorem mulN_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ),
    (∀ i, constantCoeff (mulN G n i) = 0) ∧
    comp1 (mulN G n) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 (mulN G n) (pt R (n := 2) d 0)) (comp1 (mulN G n) (pt R (n := 2) d 1)) ∧
    dLin (mulN G n) = (n : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  intro R inst d G n
  exact ⟨const_mulN G n, formalGroupLaw_comp_mulN_add G n (const_pt 0) (const_pt 1), dLin_mulN G n⟩

end GlobalTheory.FormalMulN
