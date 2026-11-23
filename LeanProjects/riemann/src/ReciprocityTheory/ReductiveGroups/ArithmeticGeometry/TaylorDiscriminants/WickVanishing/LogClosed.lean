import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d : ℕ}

private theorem cc_subst_lemma {σ τ : Type} [Fintype σ] {L : σ → MvPowerSeries τ k}
    (hL0 : ∀ p, constantCoeff (L p) = 0) (F : MvPowerSeries σ k) :
    constantCoeff (MvPowerSeries.subst L F) = constantCoeff F := by
  classical
  have hL : MvPowerSeries.HasSubst L := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hL, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact he (Finsupp.ext hn)
    have hz : constantCoeff (e.prod fun s n => L s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, hL0, zero_pow hp]
    rw [hz, smul_zero]

theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma (σ := Fin m × Fin d) (τ := Fin n × Fin d) (L := fun p => a p.1 p.2) (fun p => ha p.1 p.2) f

variable (G : FGLaw k d)

theorem formalFamilyConstantCoeffZero_zero_secondVar : CZ (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem cc_jac (i b : Fin d) : constantCoeff (Jac G i b) = if i = b then 1 else 0 := by
  have hE : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := by
    intro j i
    fin_cases j <;> simp [pt]
  have h := congrArg (pderiv k ((0 : Fin 1), b)) (G.unit i)
  rw [pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  have h2 := congrArg constantCoeff h
  rw [cc_ev formalFamilyConstantCoeffZero_zero_secondVar] at h2
  show constantCoeff (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))) = _
  rw [cc_ev hE, h2]
  by_cases hib : i = b
  · subst hib
    simp
  · simp [hib, Ne.symm hib]

def JM : Matrix (Fin d) (Fin d) (PS k 1 d) := Matrix.of (Jac G)

def Om : Matrix (Fin d) (Fin d) (PS k 1 d) := (JM G)⁻¹

theorem jm_map_cc : (JM G).map constantCoeff = 1 := by
  ext i b
  simp [JM, Matrix.one_apply, cc_jac]

theorem isUnit_det_jm : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : (constantCoeff : PS k 1 d →+* k).mapMatrix (JM G) = 1 := jm_map_cc G
  rw [h, Matrix.det_one]
  exact isUnit_one

theorem om_mul : Om G * JM G = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_jm G)

theorem mul_om : JM G * Om G = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_jm G)

theorem map_ev_mul {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (M N : Matrix (Fin d) (Fin d) (PS k m d)) :
    (M * N).map (ev a) = M.map (ev a) * N.map (ev a) := by
  let f : PS k m d →+* PS k n d :=
    { toFun := ev a
      map_one' := by simpa using ev_C ha (1 : k)
      map_mul' := ev_mul ha
      map_zero' := by simpa using ev_C ha (0 : k)
      map_add' := ev_add ha }
  exact Matrix.map_mul (f := f)

theorem map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by
  exact Matrix.map_one (ev a) (by simpa using ev_C ha (0 : k)) (by simpa using ev_C ha (1 : k))

theorem cc_om : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map (constantCoeff : PS k 1 d →+* k)) (om_mul G)
  simp only [Matrix.map_mul] at h
  first
    | (rw [jm_map_cc, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h; exact h)
    | (simpa [jm_map_cc] using h)

theorem om_Q (i b : Fin d) : ∑ j, ev (n := 2) ![G.F] (Om G i j) * Ar G j b = ev (n := 2) ![pt k d 1] (Om G i b) := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  have hY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simp [pt]
  have hJ : (JM G).map (ev (n := 2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by
    refine Matrix.ext fun i b => ?_
    rw [Matrix.mul_apply]
    exact jac_F G i b
  have h1 : (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by
    rw [← map_ev_mul hF, om_mul, map_ev_one hF]
  have h2 : (JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by
    rw [← map_ev_mul hY, mul_om, map_ev_one hY]
  have h3 : (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by
    calc (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G)
        = (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) *
            ((JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1])) := by
          rw [h2, Matrix.mul_one]
      _ = (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) *
            (Om G).map (ev (n := 2) ![pt k d 1]) := by
          rw [hJ]
          simp only [Matrix.mul_assoc]
      _ = (Om G).map (ev (n := 2) ![pt k d 1]) := by
          rw [h1, Matrix.one_mul]
  have h4 := congrFun (congrFun h3 i) b
  rw [Matrix.mul_apply] at h4
  first
    | exact h4
    | simpa using h4

theorem czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := by
  intro j i
  fin_cases j <;> simp [pt]
theorem czX : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := by
  intro j i
  fin_cases j <;> simp [pt]

theorem sw_F (h : PS k 1 d) : ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![G.F] h) = ev (n := 2) ![G.F] h := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  rw [ev_ev czSw hF]
  congr 1
  funext j i
  fin_cases j
  simpa using G.comm i

theorem sw_y (h : PS k 1 d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 0] h := by
  have hY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simp [pt]
  rw [ev_ev czSw hY]
  congr 1
  funext j i
  fin_cases j
  first
    | exact ev_X czSw 1 i
    | (simp only [Matrix.cons_val_zero]; exact ev_X czSw 1 i)
    | simp [pt, ev_X czSw]

theorem sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by
  have h := congrArg (pderiv k ((0 : Fin 2), b)) (G.comm j)
  rw [pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  first
    | exact h
    | simpa using h

theorem om_P (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv k ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  let f : PS k 2 d →+* PS k 2 d :=
    { toFun := ev (n := 2) ![pt k d 1, pt k d 0]
      map_one' := by simpa using ev_C czSw (1 : k)
      map_mul' := ev_mul czSw
      map_zero' := by simpa using ev_C czSw (0 : k)
      map_add' := ev_add czSw }
  have hs : ∀ (s : Finset (Fin d)) (g : Fin d → PS k 2 d),
      ev (n := 2) ![pt k d 1, pt k d 0] (∑ j ∈ s, g j) = ∑ j ∈ s, ev (n := 2) ![pt k d 1, pt k d 0] (g j) :=
    fun s g => map_sum f g s
  rw [hs, sw_y] at h
  simp only [ev_mul czSw, sw_F, Ar, sw_dF] at h
  exact h

theorem d_evF (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  rw [pderiv_ev hF, Fintype.sum_prod_type]
  simp

private theorem CZ_pt_vector : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := by
  intro j i
  fin_cases j <;> simp [pt]

private theorem CZ_singleton_F : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
  intro j i
  fin_cases j
  simpa using G.const i

private theorem ev_coordinate_F (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  rw [← G.comm i, ev_ev CZ_pt_vector czSw]
  have e : (fun j i' => ev (n := 1) ![pt k d 0, 0] ((![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) j i')) =
      (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
    funext j i'
    fin_cases j
    · first
        | exact ev_X CZ_pt_vector 1 i'
        | simp [pt, ev_X CZ_pt_vector]
    · first
        | exact ev_X CZ_pt_vector 0 i'
        | simp [pt, ev_X CZ_pt_vector]
  rw [e, G.unit i]

theorem ez_F (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev CZ_pt_vector (CZ_singleton_F G)]
  have e : (fun j i => ev (n := 1) ![pt k d 0, 0] ((![G.F] : Fin 1 → Pt k 2 d) j i)) =
      fun j => pt k (n := 1) d j := by
    funext j i
    fin_cases j
    exact ev_coordinate_F G i
  rw [e, ev_pt]

theorem ez_dx (j a : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (G.F j)) = if j = a then 1 else 0 := by
  have h := congrArg (pderiv k ((0 : Fin 1), a)) (ev_coordinate_F G j)
  rw [pderiv_ev CZ_pt_vector, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  first
    | exact h
    | simpa [eq_comm] using h

theorem ez_dy (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl

private theorem mvPowerSeries_pderiv_comm {σ : Type} (i j : σ) (f : MvPowerSeries σ k) :
    pderiv k i (pderiv k j f) = pderiv k j (pderiv k i f) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    MvPowerSeries.coeff_pderiv]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [add_right_comm n (Finsupp.single i 1) (Finsupp.single j 1)]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij), add_zero]
    ring

theorem om_key (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv k ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv k ((0 : Fin 1), c) (Om G i a) * Jac G c b := by
  have hE := CZ_pt_vector (k := k) (d := d)
  let fE : PS k 2 d →+* PS k 1 d :=
    { toFun := ev (n := 1) ![pt k d 0, 0]
      map_one' := by simpa using ev_C hE (1 : k)
      map_mul' := ev_mul hE
      map_zero' := by simpa using ev_C hE (0 : k)
      map_add' := ev_add hE }
  have hsE : ∀ g : Fin d → PS k 2 d,
      ev (n := 1) ![pt k d 0, 0] (∑ j, g j) = ∑ j, ev (n := 1) ![pt k d 0, 0] (g j) :=
    fun g => map_sum fE g Finset.univ
  have hz0 : ev (n := 1) ![pt k d 0, 0] (0 : PS k 2 d) = 0 := map_zero fE
  have hdJ : ∀ j, pderiv k ((0 : Fin 1), a) (Jac G j b) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (pderiv k ((1 : Fin 2), b) (G.F j))) := by
    intro j
    show pderiv k ((0 : Fin 1), a) (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F j))) = _
    rw [pderiv_ev hE, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply]
  have hR : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] (Om G i a)) = 0 := by
    rw [pderiv_ev czX, Fintype.sum_prod_type]
    simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply]
  have hP := congrArg (⇑(pderiv k ((1 : Fin 2), b))) (om_P G i a)
  rw [hR, map_sum] at hP
  simp only [Derivation.leibniz, smul_eq_mul, d_evF] at hP
  have hP2 := congrArg (ev (n := 1) ![pt k d 0, 0]) hP
  simp only [hsE, hz0, ev_mul hE, ev_add hE, ez_F, ez_dx, ez_dy,
    mvPowerSeries_pderiv_comm ((1 : Fin 2), b) ((0 : Fin 2), a), ← hdJ] at hP2
  rw [Finset.sum_add_distrib] at hP2
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hP2
  have hM := congrFun (congrFun (om_mul G) i) b
  rw [Matrix.mul_apply] at hM
  simp only [JM, Matrix.of_apply] at hM
  have hM2 := congrArg (⇑(pderiv k ((0 : Fin 1), a))) hM
  have hone : pderiv k ((0 : Fin 1), a) ((1 : Matrix (Fin d) (Fin d) (PS k 1 d)) i b) = 0 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [hone, map_sum] at hM2
  simp only [Derivation.leibniz, smul_eq_mul] at hM2
  rw [Finset.sum_add_distrib] at hM2
  linear_combination hM2 - hP2

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
