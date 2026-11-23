import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogPoinc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem om_closed (i a c : Fin d) :
    pderiv k ((0 : Fin 1), c) (Om G i a) = pderiv k ((0 : Fin 1), a) (Om G i c) := by
  set M : Fin d → PS k 1 d := fun e => pderiv k ((0 : Fin 1), e) (Om G i a) - pderiv k ((0 : Fin 1), a) (Om G i e)
    with hMdef
  have hM : ∀ b, ∑ e, M e * Jac G e b = 0 := by
    intro b
    simp only [hMdef, sub_mul, Finset.sum_sub_distrib]
    rw [← om_key G i a b]
    simp only [mul_comm, sub_self]
  have h1 : M c = ∑ e, M e * (JM G * Om G) e c := by
    rw [mul_om]
    simp [Matrix.one_apply]
  have h2 : ∑ e, M e * (JM G * Om G) e c = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hM b
    simp only [JM, Matrix.of_apply]
    rw [show ∑ x, M x * (Jac G x b * Om G b c) = (∑ x, M x * Jac G x b) * Om G b c by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring, this, zero_mul]
  have h3 : M c = 0 := h1.trans h2
  exact sub_eq_zero.1 h3

theorem d_evY (h : PS k 1 d) (b : Fin d) :
    pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) h) := by
  have hXd : ∀ v w : Fin 2 × Fin d, pderiv k v (X w : PS k 2 d) = if v = w then 1 else 0 := by
    intro v w
    first
    | (simp [MvPowerSeries.pderiv_X, Pi.single_apply]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X]; done)
    | (by_cases hvw : v = w
       · subst hvw
         simp
       · simp [hvw])
  have hcz : CZ (![pt k d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((1 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  rw [pderiv_ev hcz, Fintype.sum_eq_single ((0 : Fin 1), b)]
  · show ev _ (pderiv k ((0 : Fin 1), b) h) * pderiv k ((1 : Fin 2), b) (X ((1 : Fin 2), b)) = _
    rw [hXd, if_pos rfl, mul_one]
  · rintro ⟨j, i⟩ hne
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show ev _ _ * pderiv k ((1 : Fin 2), b) (X ((1 : Fin 2), i)) = 0
    rw [hXd, if_neg, mul_zero]
    intro heq
    apply hne
    rw [(Prod.mk.inj heq).2]

theorem d_evX (h : PS k 1 d) (a : Fin d) :
    pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 0] h) = ev (n := 2) ![pt k d 0] (pderiv k ((0 : Fin 1), a) h) := by
  have hXd : ∀ v w : Fin 2 × Fin d, pderiv k v (X w : PS k 2 d) = if v = w then 1 else 0 := by
    intro v w
    first
    | (simp [MvPowerSeries.pderiv_X, Pi.single_apply]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X]; done)
    | (by_cases hvw : v = w
       · subst hvw
         simp
       · simp [hvw])
  have hcz : CZ (![pt k d 0] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((0 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  rw [pderiv_ev hcz, Fintype.sum_eq_single ((0 : Fin 1), a)]
  · show ev _ (pderiv k ((0 : Fin 1), a) h) * pderiv k ((0 : Fin 2), a) (X ((0 : Fin 2), a)) = _
    rw [hXd, if_pos rfl, mul_one]
  · rintro ⟨j, i⟩ hne
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show ev _ _ * pderiv k ((0 : Fin 2), a) (X ((0 : Fin 2), i)) = 0
    rw [hXd, if_neg, mul_zero]
    intro heq
    apply hne
    rw [(Prod.mk.inj heq).2]

theorem pderiv_first_ev_second_point_eq_zero (h : PS k 1 d) (a : Fin d) : pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 1] h) = 0 := by
  have hXd : ∀ v w : Fin 2 × Fin d, pderiv k v (X w : PS k 2 d) = if v = w then 1 else 0 := by
    intro v w
    first
    | (simp [MvPowerSeries.pderiv_X, Pi.single_apply]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X]; done)
    | (by_cases hvw : v = w
       · subst hvw
         simp
       · simp [hvw])
  have hcz : CZ (![pt k d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((1 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  rw [pderiv_ev hcz]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨j, i⟩ := p
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show ev _ _ * pderiv k ((0 : Fin 2), a) (X ((1 : Fin 2), i)) = 0
  rw [hXd, if_neg, mul_zero]
  intro heq
  exact absurd (Prod.mk.inj heq).1 (by decide)

theorem pderiv_second_ev_first_point_eq_zero (h : PS k 1 d) (b : Fin d) : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] h) = 0 := by
  have hXd : ∀ v w : Fin 2 × Fin d, pderiv k v (X w : PS k 2 d) = if v = w then 1 else 0 := by
    intro v w
    first
    | (simp [MvPowerSeries.pderiv_X, Pi.single_apply]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X]; done)
    | (by_cases hvw : v = w
       · subst hvw
         simp
       · simp [hvw])
  have hcz : CZ (![pt k d 0] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((0 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  rw [pderiv_ev hcz]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨j, i⟩ := p
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show ev _ _ * pderiv k ((1 : Fin 2), b) (X ((0 : Fin 2), i)) = 0
  rw [hXd, if_neg, mul_zero]
  intro heq
  exact absurd (Prod.mk.inj heq).1 (by decide)

variable [Algebra ℚ k]

def logOf (i : Fin d) : PS k 1 d := prim (fun v : Fin 1 × Fin d => Om G i v.2)

theorem pderiv_logOf (i a : Fin d) : pderiv k ((0 : Fin 1), a) (logOf G i) = Om G i a := by
  unfold logOf
  refine pderiv_prim _ ?_ _
  rintro ⟨a0, a'⟩ ⟨c0, c'⟩
  have h0 : a0 = 0 := Subsingleton.elim _ _
  have h1 : c0 = 0 := Subsingleton.elim _ _
  subst h0 h1
  exact om_closed G i a' c'

theorem logOf_add (i : Fin d) :
    ev (n := 2) ![G.F] (logOf G i) = ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i) := by
  rw [← sub_eq_zero]
  set g := ev (n := 2) ![G.F] (logOf G i) - (ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i))
  have hd : ∀ v, pderiv k v g = 0 := by
    rintro ⟨j, c⟩
    fin_cases j
    · simp only [Fin.zero_eta]
      simp only [g, map_sub, map_add, d_evF, pderiv_logOf, pderiv_first_ev_second_point_eq_zero, d_evX]
      rw [om_P G i c]; ring
    · simp only [Fin.mk_one]
      simp only [g, map_sub, map_add, d_evF, pderiv_logOf, pderiv_second_ev_first_point_eq_zero, d_evY]
      have := om_Q G i c
      simp only [Ar] at this
      rw [this]; ring
  have hc : constantCoeff g = 0 := by
    simp only [g, map_sub, map_add, cc_ev (czFF G), cc_ev czX, cc_ev czY, logOf, constantCoeff_prim]
    ring
  rw [eq_C_of_pderiv_zero hd, hc, map_zero]

theorem addPt : (![G.add (pt k (n := 2) d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) = ![G.F] := by
  have hid : ∀ f : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
    intro f
    have hfam : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) p.1 p.2) =
        fun p => (X p : PS k 2 d) := by
      funext p
      obtain ⟨j, i⟩ := p
      fin_cases j <;> rfl
    unfold ev
    rw [hfam]
    first
    | exact congrFun MvPowerSeries.subst_self f
    | (rw [MvPowerSeries.subst_self]; rfl)
    | simp [MvPowerSeries.subst_self]
  funext j i
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact hid (G.F i)

theorem logSt : LogSt := by
  intro k _ _ d G
  refine ⟨fun i => logOf G i, fun i => constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (logOf G i) = (1 : Matrix (Fin d) (Fin d) k) i j
    have h := congrArg constantCoeff (pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · funext i
    show ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (logOf G i) =
      ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i)
    rw [addPt]
    exact logOf_add G i

omit [Algebra ℚ k] in
theorem ez_y (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] h) = C (constantCoeff h) := by
  have ha : CZ (![pt k d 0, 0] : Fin 2 → Pt k 1 d) := by
    intro j i
    fin_cases j
    · show constantCoeff (X ((0 : Fin 1), i) : PS k 1 d) = 0
      first
      | exact MvPowerSeries.constantCoeff_X _
      | simp
    · show constantCoeff (0 : PS k 1 d) = 0
      exact map_zero _
  have hb : CZ (![pt k d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((1 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  have hc : CZ (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) := fun j => Fin.elim0 j
  have hz : CZ (fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) := fun _ _ => map_zero _
  have hev0 : ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) (0 : PS k 0 d) = 0 := by
    have h0 := ev_sub hc (0 : PS k 0 d) 0
    simp only [sub_self] at h0
    exact h0
  have hfam : (fun (j : Fin 1) (i : Fin d) =>
      ev (![pt k d 0, 0] : Fin 2 → Pt k 1 d) ((![pt k d 1] : Fin 1 → Pt k 2 d) j i)) =
      fun (j : Fin 1) (i : Fin d) => ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d))
        ((fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) j i) := by
    funext j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show ev (![pt k d 0, 0] : Fin 2 → Pt k 1 d) (X ((1 : Fin 2), i)) =
      ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) (0 : PS k 0 d)
    rw [hev0, ev_X ha]
    all_goals rfl
  have hconst : ∀ g : PS k 0 d, g = C (constantCoeff g) := by
    intro g
    ext e
    have he : e = 0 := by
      first
      | exact Subsingleton.elim _ _
      | exact Finsupp.ext fun p => Fin.elim0 p.1
    subst he
    first
    | (simp; done)
    | rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [ev_ev ha hb, hfam, ← ev_ev hc hz, hconst (ev (fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) h),
    cc_ev hz, ev_C hc]

theorem logDerivSt : LogDerivSt := by
  intro k _ _ d G ℓ h0 h1 hadd u g
  have hℓ : CZ (![ℓ] : Fin 1 → Pt k 1 d) := CZ.cons h0 CZ.nil
  have hadd' : ∀ c, ev (n := 2) ![G.F] (ℓ c) = ev (n := 2) ![pt k d 0] (ℓ c) + ev (n := 2) ![pt k d 1] (ℓ c) := by
    intro c
    have := congrFun hadd c
    change ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ c) = _ at this
    rwa [addPt] at this
  have DJ : ∀ c b, ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j b = C (if c = b then 1 else 0) := by
    intro c b
    have h := congrArg (fun x => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) x)) (hadd' c)
    beta_reduce at h
    simp only [d_evF, map_add, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ev_sum cz1, ev_mul cz1, ez_F, ez_dy, ez_y] at h
    rw [h]
    congr 1
    have hc := congrFun (congrFun h1 c) b
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp only [dLin] at hc
    simp [hc, Matrix.one_apply]
  have hch : ∀ j, pderiv k ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) =
      ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c) := by
    intro j
    rw [pderiv_ev hℓ, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  have step : ∀ c, ∑ i, C (u i) * ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j i = (C (u c) : PS k 1 d) := by
    intro c
    simp only [DJ, ← map_mul, mul_ite, mul_one, mul_zero]
    rw [← map_sum]
    simp [Finset.sum_ite_eq]
  show ∑ j : Fin d, (∑ i : Fin d, C (u i) * Jac G j i) * pderiv k ((0 : Fin 1), j) (ev (n := 1) ![ℓ] g) = _
  simp only [hch]
  rw [ev_sum hℓ]
  calc ∑ j, (∑ i, C (u i) * Jac G j i) *
        ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)
      = ∑ j, ∑ c, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_comm]
    _ = ∑ c, ∑ j, ∑ i, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ j, C (u i) * Jac G j i *
          (ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) * pderiv k ((0 : Fin 1), j) (ℓ c)) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ev (n := 1) ![ℓ] (pderiv k ((0 : Fin 1), c) g) *
          ∑ i, C (u i) * ∑ j, pderiv k ((0 : Fin 1), j) (ℓ c) * Jac G j i := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [step, ev_mul hℓ, ev_C hℓ, mul_comm]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
