import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntAASubstOfHasSubst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.GaugeAdjoint

open GlobalTheory.FormalCalc GlobalTheory.IntSeries

section Ev

variable {k : Type} [CommRing k] {d m n p : ℕ}

theorem hasSubst_pts {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun q : Fin m × Fin d => a q.1 q.2) := hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have hs := hasSubst_pts ha
  have hsplit : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  unfold ev
  conv_lhs => rw [hsplit]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs (fun q => ha q.1 q.2) h0, add_zero]
  simp

theorem ev_ev {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply (hasSubst_pts ha) (hasSubst_pts hb)]

theorem ev_pt {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m)
    (i : Fin d) : ev a (pt k d j i) = a j i := by
  unfold ev pt
  rw [subst_X (hasSubst_pts ha)]

theorem ev_zero {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    ev a (0 : PS k m d) = 0 := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_zero]

private theorem coeff_subst_congr_lemma {σ τ : Type} [Finite σ] [Finite τ] {A : σ → MvPowerSeries τ k}
    (hA : ∀ q, constantCoeff (A q) = 0) {g g' : MvPowerSeries σ k} {x : τ →₀ ℕ}
    (hgg : ∀ y : σ →₀ ℕ, y.degree ≤ x.degree → coeff y g = coeff y g') :
    coeff x (subst A g) = coeff x (subst A g') := by
  have hT : truncTotal (x.degree + 1) g = truncTotal (x.degree + 1) g' := by
    ext y
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hy
    · exact hgg y (Nat.lt_succ_iff.mp hy)
    · rfl
  have e1 := congrArg (MvPolynomial.coeff x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g) hA)
  have e2 := congrArg (MvPolynomial.coeff x)
    (truncTotal_subst_eq_truncTotal_truncTotal_subst (k := x.degree + 1) (f := g') hA)
  rw [coeff_truncTotal _ (Nat.lt_succ_self _)] at e1 e2
  rw [e1, e2, hT]

private theorem pderiv_subst_coe_mvPolynomial_eq_sum {σ τ : Type} [Fintype σ] [DecidableEq σ]
    {A : σ → MvPowerSeries τ k} (hA : HasSubst A) (s : τ) (q : MvPolynomial σ k) :
    pderiv k s (subst A (q : MvPowerSeries σ k)) =
      ∑ r, subst A (pderiv k r (q : MvPowerSeries σ k)) * pderiv k s (A r) := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.coe_C, subst_C, pderiv_C]
    symm
    apply Finset.sum_eq_zero
    intro r _
    rw [pderiv_C, ← substAlgHom_apply hA, map_zero, zero_mul]
  | add f g hf hg =>
    simp only [MvPolynomial.coe_add, subst_add hA, map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f r0 hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
    simp only [← substAlgHom_apply hA] at hf ⊢
    have hX : ∀ r, substAlgHom hA (pderiv k r (X r0 : MvPowerSeries σ k)) = if r = r0 then 1 else 0 := by
      intro r
      split_ifs with hr
      · subst hr
        rw [pderiv_X_self, map_one]
      · rw [pderiv_X_of_ne (Ne.symm hr), map_zero]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, substAlgHom_X, hX, hf, mul_ite,
      mul_one, mul_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

private theorem pderiv_subst_eq_sum_of_constantCoeff_eq_zero {σ τ : Type} [Fintype σ] [DecidableEq σ] [Finite τ]
    {A : σ → MvPowerSeries τ k} (hA : ∀ r, constantCoeff (A r) = 0) (f : MvPowerSeries σ k) (s : τ) :
    pderiv k s (subst A f) = ∑ r, subst A (pderiv k r f) * pderiv k s (A r) := by
  classical
  have hS : HasSubst A := hasSubst_of_constantCoeff_zero hA
  ext x
  have h1 : coeff (x + Finsupp.single s 1) (subst A f) =
      coeff (x + Finsupp.single s 1)
        (subst A ((truncTotal (x.degree + 2) f : MvPolynomial σ k) : MvPowerSeries σ k)) := by
    apply coeff_subst_congr_lemma hA
    intro z hz
    rw [MvPolynomial.coeff_coe, coeff_truncTotal]
    rw [map_add, Finsupp.degree_single] at hz
    omega
  rw [coeff_pderiv, h1, ← coeff_pderiv, pderiv_subst_coe_mvPolynomial_eq_sum hS]
  simp only [map_sum, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun y hy => ?_
  congr 1
  apply coeff_subst_congr_lemma hA
  intro z hz
  have hxy := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  have h2 : y.1.degree ≤ x.degree := by
    rw [← hxy, map_add]
    omega
  rw [coeff_pderiv, coeff_pderiv, MvPolynomial.coeff_coe, coeff_truncTotal]
  rw [map_add, Finsupp.degree_single]
  omega

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) (s : Fin n × Fin d) :
    pderiv k s (ev a f) = ∑ j, ∑ i, ev a (pderiv k (j, i) f) * pderiv k s (a j i) := by
  unfold ev
  rw [pderiv_subst_eq_sum_of_constantCoeff_eq_zero (A := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2),
    Fintype.sum_prod_type]

theorem const_pt (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by
  unfold pt
  exact constantCoeff_X _

theorem const_one {x : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![x] : Fin 1 → Pt k n d) j i) = 0 := by
  fin_cases j
  simpa using hx i

theorem const_two {x y : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Pt k n d) j i) = 0 := by
  fin_cases j
  · simpa using hx i
  · simpa using hy i

theorem const_zero (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by simp

theorem const_comp1 {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) {x : Pt k n d}
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 φ x i) = 0 := by
  unfold comp1
  rw [constantCoeff_ev (const_one hx)]
  exact hφ i

theorem ev_origin (f : PS k 1 d) : ev (n := n) ![0] f = C (constantCoeff f) := by
  have hz : (fun q : Fin 1 × Fin d => (![0] : Fin 1 → Pt k n d) q.1 q.2) = 0 := by
    funext q
    simp
  unfold ev
  rw [hz, subst_zero_eq_C_constantCoeff]
  simp

theorem ev_ev_one {x : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by
  rw [ev_ev (const_one hx) hb]
  congr 1
  funext j
  fin_cases j
  rfl

theorem ev_ev_two {x y : Pt k n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0)
    {b : Fin n → Pt k p d} (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k 2 d) :
    ev b (ev ![x, y] f) = ev ![fun i => ev b (x i), fun i => ev b (y i)] f := by
  rw [ev_ev (const_two hx hy) hb]
  congr 1
  funext j
  fin_cases j
  · rfl
  · rfl

theorem const_axis (j : Fin 2) (i : Fin d) :
    constantCoeff ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
  fin_cases j
  · simpa using const_pt 0 i
  · simp

theorem axis_pt_zero :
    (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (0 : Fin 2) i)) = pt k d 0 := by
  funext i
  rw [ev_pt const_axis]
  rfl

theorem axis_pt_one : (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (1 : Fin 2) i)) = 0 := by
  funext i
  rw [ev_pt const_axis]
  rfl

theorem axis_left {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] f) =
      ev (n := 1) ![comp1 φ (pt k d 0)] (ev (n := 1) ![pt k d 0, 0] f) := by
  have hp0 : ∀ i, constantCoeff (pt k d (0 : Fin 2) i) = 0 := fun i => const_pt 0 i
  have hp1 : ∀ i, constantCoeff (pt k d (1 : Fin 2) i) = 0 := fun i => const_pt 1 i
  have hq0 : ∀ i, constantCoeff (pt k d (0 : Fin 1) i) = 0 := fun i => const_pt 0 i
  have hc0 := const_comp1 hφ hp0
  have hb0 := const_comp1 hφ hq0
  rw [ev_ev_two hc0 hp1 const_axis, ev_ev_two hq0 (fun i => const_zero i) (const_one hb0)]
  have e0 : (fun i => ev (n := 1) ![pt k d 0, 0] (comp1 φ (pt k d (0 : Fin 2)) i)) =
      fun i => ev (n := 1) ![comp1 φ (pt k d (0 : Fin 1))] (pt k d (0 : Fin 1) i) := by
    funext i
    rw [ev_pt (const_one hb0)]
    show ev _ (ev ![pt k d 0] (φ i)) = ev ![pt k d 0] (φ i)
    rw [ev_ev_one hp0 const_axis, axis_pt_zero]
  have e1 : (fun i => ev (n := 1) ![pt k d 0, 0] (pt k d (1 : Fin 2) i)) =
      fun i => ev (n := 1) ![comp1 φ (pt k d (0 : Fin 1))] ((0 : Pt k 1 d) i) := by
    rw [axis_pt_one]
    funext i
    exact (ev_zero (const_one hb0)).symm
  rw [e0, e1]

theorem axis_right {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] f) =
      ev (n := 1) ![pt k d 0, 0] f := by
  have hp0 : ∀ i, constantCoeff (pt k d (0 : Fin 2) i) = 0 := fun i => const_pt 0 i
  have hp1 : ∀ i, constantCoeff (pt k d (1 : Fin 2) i) = 0 := fun i => const_pt 1 i
  have hc1 := const_comp1 hφ hp1
  have e1 : (fun i => ev (n := 1) ![pt k d 0, 0] (comp1 φ (pt k d (1 : Fin 2)) i)) = 0 := by
    funext i
    show ev _ (ev ![pt k d 1] (φ i)) = 0
    rw [ev_ev_one hp1 const_axis, axis_pt_one, ev_origin, hφ i, map_zero]
  rw [ev_ev_two hp0 hc1 const_axis, axis_pt_zero, e1]

theorem pderiv_pt (j j' : Fin n) (i i' : Fin d) :
    pderiv k (j, i) (pt k d j' i') = if j' = j ∧ i' = i then 1 else 0 := by
  unfold pt
  by_cases hc : j' = j ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := hc
    simp
  · rw [if_neg hc, pderiv_X_of_ne]
    intro he
    exact hc ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem pderiv_comp1 (φ : Pt k 1 d) (j j' : Fin n) (i l : Fin d) :
    pderiv k (j, i) (comp1 φ (pt k d j') l) =
      if j' = j then ev ![pt k d j'] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by
  show pderiv k (j, i) (ev ![pt k d j'] (φ l)) = _
  rw [pderiv_ev (const_one (fun i => const_pt j' i))]
  by_cases hj : j' = j
  · subst hj
    simp [pderiv_pt]
  · simp [pderiv_pt, hj]

theorem pderiv_left {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d)
    (i : Fin d) :
    pderiv k ((1 : Fin 2), i) (ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] f) =
      ev (n := 2) ![comp1 φ (pt k d 0), pt k d 1] (pderiv k ((1 : Fin 2), i) f) := by
  rw [pderiv_ev (const_two (const_comp1 hφ (fun i => const_pt 0 i)) (fun i => const_pt 1 i))]
  simp [Fin.sum_univ_two, pderiv_comp1, pderiv_pt]

theorem pderiv_right {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : PS k 2 d)
    (i : Fin d) :
    pderiv k ((1 : Fin 2), i) (ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] f) =
      ∑ j, ev (n := 2) ![pt k d 0, comp1 φ (pt k d 1)] (pderiv k ((1 : Fin 2), j) f) *
        ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), i) (φ j)) := by
  rw [pderiv_ev (const_two (fun i => const_pt 0 i) (const_comp1 hφ (fun i => const_pt 1 i)))]
  simp [Fin.sum_univ_two, pderiv_comp1, pderiv_pt]

theorem axis_pderiv (φ : PS k 1 d) (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), i) φ)) =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) φ) := by
  rw [ev_ev_one (fun i => const_pt 1 i) const_axis, axis_pt_one, ev_origin]
  congr 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

private theorem ev_sub_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS k m d) :
    ev a (f - g) = ev a f - ev a g := by
  unfold ev
  exact subst_sub (hasSubst_pts ha) f g

private theorem ev_mul_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS k m d) :
    ev a (f * g) = ev a f * ev a g := by
  unfold ev
  exact subst_mul (hasSubst_pts ha) f g

private theorem ev_neg_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) :
    ev a (-f) = -ev a f := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_neg, substAlgHom_apply]

private theorem ev_finset_sum_of_constantCoeff_eq_zero {a : Fin m → Pt k n d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type} (s : Finset ι) (F : ι → PS k m d) :
    ev a (∑ j ∈ s, F j) = ∑ j ∈ s, ev a (F j) := by
  unfold ev
  rw [← substAlgHom_apply (hasSubst_pts ha), map_sum]
  simp only [substAlgHom_apply]

private theorem pderiv_map_algebraMap' {R : Type} [CommRing R] [Algebra R k] {σ : Type} (s : σ)
    (W : MvPowerSeries σ R) :
    pderiv k s (map (algebraMap R k) W) = map (algebraMap R k) (pderiv R s W) := by
  ext x
  rw [coeff_pderiv, coeff_map, coeff_map, coeff_pderiv, map_mul]
  simp

private theorem ev_formalExp_of_constantCoeff_eq_zero [Algebra ℚ k]
    {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS k m d}
    (hf : constantCoeff f = 0) : ev a (formalExp f) = formalExp (ev a f) := by
  unfold ev
  exact subst_formalExp (hasSubst_pts ha) hf

private theorem ev_axis_map_algebraMap {R : Type} [CommRing R] [Algebra R k]
    (W : PS R 2 d) :
    ev (n := 1) ![pt k d 0, 0] (map (algebraMap R k) W) =
      map (algebraMap R k) (ev (n := 1) ![pt R d 0, 0] W) := by
  unfold ev
  rw [map_subst (hasSubst_pts const_axis)]
  congr 1
  funext q
  obtain ⟨j, l⟩ := q
  fin_cases j <;> simp [pt]

end Ev

theorem main : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (i : Fin d), IntAA (R := R) k (ev (n := 1) ![comp1 (B.actK k a) (pt k d 0)] (sgOf k h i) - ∑ j, sgOf k h j * C (dAct k B (star a) j i)) := by
  intro R _ d O _ _ k _ _ _ B h hh a i
  have hp0 : ∀ l, constantCoeff (pt k d (0 : Fin 2) l) = 0 := fun l => const_pt 0 l
  have hp1 : ∀ l, constantCoeff (pt k d (1 : Fin 2) l) = 0 := fun l => const_pt 1 l
  have hq0 : ∀ l, constantCoeff (pt k d (0 : Fin 1) l) = 0 := fun l => const_pt 0 l
  have hact : ∀ (b : O) (l : Fin d), constantCoeff (B.actK k b l) = 0 := by
    intro b l
    show constantCoeff (map (algebraMap R k) (B.A.act b l)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      B.A.const b l, map_zero]
  have hb0 := const_one (const_comp1 (hact a) hq0)
  have hc1 := const_two (const_comp1 (hact a) hp0) hp1
  have hc2 := const_two hp0 (const_comp1 (hact (star a)) hp1)
  have hQ0 : constantCoeff (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [map_sub, constantCoeff_ev hc1, constantCoeff_ev hc2, sub_self]
  have hA : map (algebraMap R k) (B.ad a) =
      formalExp (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
        ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) := hh.ad a
  have hEQ : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := by
    rw [ev_sub_of_constantCoeff_eq_zero const_axis, axis_left (hact a), axis_right (hact (star a)), hh.ax1,
      ev_zero hb0, sub_self]
  have hE : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (map (algebraMap R k) (B.ad a))) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i)
        (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
          ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)) := by
    rw [hA, pderiv_formalExp hQ0, ev_mul_of_constantCoeff_eq_zero const_axis, ev_formalExp_of_constantCoeff_eq_zero const_axis hQ0, hEQ,
      formalExp_zero, one_mul]
  have hsg : ∀ j, ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) h) = -sgOf k h j := by
    intro j
    simp only [sgOf, neg_neg]
  have key : ev (n := 1) ![comp1 (B.actK k a) (pt k d 0)] (sgOf k h i) -
      ∑ j, sgOf k h j * C (dAct k B (star a) j i) =
      -ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (map (algebraMap R k) (B.ad a))) := by
    rw [hE, map_sub, ev_sub_of_constantCoeff_eq_zero const_axis, pderiv_left (hact a), pderiv_right (hact (star a)),
      axis_left (hact a), ev_finset_sum_of_constantCoeff_eq_zero const_axis]
    simp only [ev_mul_of_constantCoeff_eq_zero const_axis, axis_right (hact (star a)), axis_pderiv, hsg, ev_neg_of_constantCoeff_eq_zero hb0,
      dAct, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [key, pderiv_map_algebraMap', ev_axis_map_algebraMap]
  intro x
  exact RingHom.mem_range.mpr ⟨-coeff x (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (B.ad a))),
    by simp [coeff_map]⟩

end GlobalTheory.GaugeAdjoint
