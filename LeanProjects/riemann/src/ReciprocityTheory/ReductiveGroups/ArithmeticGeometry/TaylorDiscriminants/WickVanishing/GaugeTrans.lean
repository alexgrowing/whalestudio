import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

section Exp2

variable (A : Type) [CommRing A] [Algebra ℚ A]

theorem gt_coeff_X_pow (i : Fin 2) (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X i : MvPowerSeries (Fin 2) A) ^ n) = if e = single i n then 1 else 0 := by
  first
    | exact MvPowerSeries.coeff_X_pow e i n
    | (classical exact MvPowerSeries.coeff_X_pow e i n)
    | simp [MvPowerSeries.coeff_X_pow]

theorem gt_coeff_expX (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) A) (PowerSeries.exp A)) =
      if e = single i (e i) then algebraMap ℚ A (1 / (e i).factorial) else 0 := by
  have ha : PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha]
  simp_rw [gt_coeff_X_pow A i, PowerSeries.coeff_exp]
  rw [finsum_eq_single _ (e i)]
  · split_ifs <;> simp
  · intro m hm
    split_ifs with h
    · exact absurd (by rw [h]; simp) hm
    · simp

theorem gt_single_add (e : Fin 2 →₀ ℕ) : e = single 0 (e 0) + single 1 (e 1) := by
  ext j
  fin_cases j <;> simp [Finsupp.single_apply]

theorem gt_coeff_sum_pow (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e (((X 0 : MvPowerSeries (Fin 2) A) + X 1) ^ n) =
      if e 0 + e 1 = n then ((n.choose (e 0) : ℕ) : A) else 0 := by
  have hterm : ∀ m, coeff e ((X 0 : MvPowerSeries (Fin 2) A) ^ m * X 1 ^ (n - m) *
      ((n.choose m : ℕ) : MvPowerSeries (Fin 2) A)) =
      if e = single 0 m + single 1 (n - m) then ((n.choose m : ℕ) : A) else 0 := by
    intro m
    rw [mul_comm _ ((n.choose m : ℕ) : MvPowerSeries (Fin 2) A), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial]
    split_ifs <;> simp
  rw [add_pow, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (e 0)]
  · by_cases h : e 0 + e 1 = n
    · rw [if_pos h, if_pos]
      rw [show n - e 0 = e 1 by omega]
      exact gt_single_add e
    · rw [if_neg h]
      split_ifs with he
      · have h1 : e 1 = n - e 0 := by simpa using DFunLike.congr_fun he 1
        have hlt : n < e 0 := by omega
        rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      · rfl
  · intro b _ hb
    rw [if_neg]
    intro he
    apply hb
    have h0 : e 0 = b := by simpa using DFunLike.congr_fun he 0
    exact h0.symm
  · intro hn
    have hlt : n < e 0 := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    · rfl

theorem exp_subst_add_two_vars :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) A) + X 1) (PowerSeries.exp A) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) := by
  ext e
  have ha : PowerSeries.HasSubst ((X 0 : MvPowerSeries (Fin 2) A) + X 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha, MvPowerSeries.coeff_mul]
  simp_rw [gt_coeff_sum_pow A, gt_coeff_expX A, PowerSeries.coeff_exp]
  rw [finsum_eq_single _ (e 0 + e 1)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single (single 0 (e 0), single 1 (e 1))]
    · simp only [Finsupp.single_eq_same, eq_self_iff_true, if_true, ite_true]
      rw [smul_eq_mul, ← map_natCast (algebraMap ℚ A), ← map_mul, ← map_mul]
      congr 1
      have f0 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by positivity
      have f1 : ((e 0).factorial : ℚ) ≠ 0 := by positivity
      have f2 : ((e 1).factorial : ℚ) ≠ 0 := by positivity
      rw [Nat.cast_choose ℚ (Nat.le_add_right (e 0) (e 1)), Nat.add_sub_cancel_left]
      field_simp
      all_goals ring
    · intro p hp hne
      have hp' : p.1 + p.2 = e := by simpa using hp
      by_cases h1 : p.1 = single 0 (p.1 0)
      · by_cases h2 : p.2 = single 1 (p.2 1)
        · exfalso
          have a1 : p.2 0 = 0 := by
            rw [h2]
            simp
          have a2 : p.1 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hp' 0
          have c1 := DFunLike.congr_fun hp' 1
          simp only [Finsupp.add_apply] at c0 c1
          apply hne
          refine Prod.ext ?_ ?_
          · show p.1 = single 0 (e 0)
            rw [h1]
            congr 1
            omega
          · show p.2 = single 1 (e 1)
            rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hnot
      exfalso
      apply hnot
      simpa using (gt_single_add e).symm
  · intro d hd
    rw [if_neg (fun h => hd h.symm), smul_zero]

end Exp2

section Ev

variable {k : Type} [CommRing k] {d : ℕ}

def GP {n : ℕ} (a : Pt k n d) : Prop := ∀ i, constantCoeff (a i) = 0

theorem gt_hasSubst {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) :
    MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem gt_ev_add {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f g : PS k m d) :
    ev a (f + g) = ev a f + ev a g := by
  first
    | exact MvPowerSeries.subst_add (gt_hasSubst a ha) f g
    | exact map_add (MvPowerSeries.substAlgHom (gt_hasSubst a ha)) f g

theorem gt_ev_sub {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f g : PS k m d) :
    ev a (f - g) = ev a f - ev a g := by
  first
    | exact MvPowerSeries.subst_sub (gt_hasSubst a ha) f g
    | rw [eq_sub_iff_add_eq, ← gt_ev_add a ha, sub_add_cancel]

theorem gt_ev_mul {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f g : PS k m d) :
    ev a (f * g) = ev a f * ev a g := by
  first
    | exact MvPowerSeries.subst_mul (gt_hasSubst a ha) f g
    | exact map_mul (MvPowerSeries.substAlgHom (gt_hasSubst a ha)) f g

theorem gt_ev_zero {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) :
    ev a (0 : PS k m d) = 0 := by
  have h := gt_ev_add a ha (0 : PS k m d) 0
  rw [add_zero] at h
  first
    | linear_combination -h
    | simpa using h

theorem gt_ev_X {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (j : Fin m) (i : Fin d) :
    ev a (X (j, i) : PS k m d) = a j i := by
  first
    | exact MvPowerSeries.subst_X (gt_hasSubst a ha) (j, i)
    | simp [ev, MvPowerSeries.subst_X (gt_hasSubst a ha)]

theorem gt_ev_ev {l m n : ℕ} (a : Fin m → Pt k n d) (b : Fin l → Pt k m d) (ha : ∀ j, GP (a j))
    (hb : ∀ j, GP (b j)) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  first
    | exact MvPowerSeries.subst_comp_subst_apply (gt_hasSubst b hb) (gt_hasSubst a ha) f
    | exact MvPowerSeries.subst_comp_subst_apply (gt_hasSubst a ha) (gt_hasSubst b hb) f

private theorem gt_cc_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ k) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact he (Finsupp.ext hne)
    have h0 : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, ha s, zero_pow hs])
    rw [h0, smul_zero]

theorem gt_const_ev {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f : PS k m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  exact (gt_cc_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf

theorem gp_pt {n : ℕ} (j : Fin n) : GP (pt k d j) := by
  show ∀ i, _
  intro i
  simp [pt]

theorem gp_zero₂ {n : ℕ} : GP (0 : Pt k n d) := by
  show ∀ i, _
  intro i
  simp

theorem gp_comp1 {n : ℕ} (φ : Pt k 1 d) (a : Pt k n d) (hφ : GP φ) (ha : GP a) : GP (comp1 φ a) := by
  show ∀ i, _
  intro i
  exact gt_const_ev ![a]
    (fun j => by first | (rw [Matrix.cons_val_fin_one]; exact ha) | (fin_cases j; exact ha)) (φ i) (hφ i)

theorem gp_addOf {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (a b : Pt k n d)
    (ha : GP a) (hb : GP b) : GP (addOf F a b) := by
  show ∀ i, _
  intro i
  exact gt_const_ev ![a, b]
    (fun j => by fin_cases j <;> first | assumption | simpa using ha | simpa using hb) (F i) (hF i)

theorem gt_ev_expS [Algebra ℚ k] {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (f : PS k m d)
    (hf : constantCoeff f = 0) : ev a (FB.expS k f) = FB.expS k (ev a f) := by
  exact MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => hf)) (gt_hasSubst a ha) (PowerSeries.exp k)

private theorem gt_substExp_lemma [Algebra ℚ k] {τ : Type} {b : Fin 2 → MvPowerSeries τ k}
    (hb : MvPowerSeries.HasSubst b) (p : MvPowerSeries (Fin 2) k) (hp : constantCoeff p = 0) :
    MvPowerSeries.subst b (PowerSeries.subst p (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst b p) (PowerSeries.exp k) :=
  MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => hp)) hb _

theorem gt_expS_add [Algebra ℚ k] {n : ℕ} (f g : PS k n d) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : FB.expS k (f + g) = FB.expS k f * FB.expS k g := by
  have hb : MvPowerSeries.HasSubst (![f, g] : Fin 2 → PS k n d) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by fin_cases j <;> simp [hf, hg])
  have key := congrArg (MvPowerSeries.subst (![f, g] : Fin 2 → PS k n d)) (exp_subst_add_two_vars k)
  have e1 := gt_substExp_lemma hb ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (by simp)
  have e2 := gt_substExp_lemma hb (X 0 : MvPowerSeries (Fin 2) k) (by simp)
  have e3 := gt_substExp_lemma hb (X 1 : MvPowerSeries (Fin 2) k) (by simp)
  rw [MvPowerSeries.subst_mul hb, e1, e2, e3, MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at key
  simpa [FB.expS] using key

end Ev

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

def evP {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) : Pt k n d := fun i => ev V (a i)

theorem single_point_zero_constant {n : ℕ} {a : Pt k n d} (ha : GP a) : ∀ j, GP (![a] j) := by
  intro j
  first
    | (rw [Matrix.cons_val_fin_one]; exact ha)
    | (fin_cases j; exact ha)
    | (fin_cases j; simpa using ha)

theorem pair_points_zero_constant {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) : ∀ j, GP (![a, b] j) := by
  intro j
  fin_cases j <;> first | assumption | simpa using ha | simpa using hb

theorem triple_points_zero_constant {n : ℕ} {a b c : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) : ∀ j, GP (![a, b, c] j) := by
  intro j
  fin_cases j <;> first | assumption | simpa using ha | simpa using hb | simpa using hc

theorem gp_evP {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a : Pt k m d) (ha : GP a) :
    GP (evP V a) := by
  show ∀ i, _
  intro i
  exact gt_const_ev V hV (a i) (ha i)

theorem evP_pt {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (j : Fin m) :
    evP V (pt k d j) = V j := by
  funext i
  exact gt_ev_X V hV j i

theorem evP_comp1 {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (φ : Pt k 1 d) (a : Pt k m d)
    (ha : GP a) : evP V (comp1 φ a) = comp1 φ (evP V a) := by
  funext i
  show ev V (ev ![a] (φ i)) = ev ![evP V a] (φ i)
  rw [gt_ev_ev V ![a] hV (single_point_zero_constant ha) (φ i)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem evP_addOf {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (F : Fin d → PS k 2 d)
    (a b : Pt k m d) (ha : GP a) (hb : GP b) : evP V (addOf F a b) = addOf F (evP V a) (evP V b) := by
  funext i
  show ev V (ev ![a, b] (F i)) = ev ![evP V a, evP V b] (F i)
  rw [gt_ev_ev V ![a, b] hV (pair_points_zero_constant ha hb) (F i)]
  congr 1
  funext j l
  fin_cases j <;> rfl

theorem gt_ev_ev' {l m n : ℕ} (V : Fin m → Pt k n d) (W : Fin l → Pt k m d) (hV : ∀ j, GP (V j))
    (hW : ∀ j, GP (W j)) (f : PS k l d) : ev V (ev W f) = ev (fun j => evP V (W j)) f := gt_ev_ev V W hV hW f

theorem gt_comp1_comp1 {n : ℕ} (f g : Pt k 1 d) (hg : GP g) (a : Pt k n d) (ha : GP a) :
    comp1 (comp1 f g) a = comp1 f (comp1 g a) := by
  funext i
  show ev ![a] (ev ![g] (f i)) = ev ![comp1 g a] (f i)
  rw [gt_ev_ev ![a] ![g] (single_point_zero_constant ha) (single_point_zero_constant hg) (f i)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem gt_comp1_pt {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (pt k (n := 1) d 0) a = a := by
  funext i
  exact gt_ev_X ![a] (single_point_zero_constant ha) 0 i

theorem gt_comp_inv {n : ℕ} {φ φi : Pt k 1 d} (h : IsInvPair φ φi) (a : Pt k n d) (ha : GP a) :
    comp1 φ (comp1 φi a) = a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [← gt_comp1_comp1 φ φi h2 a ha, h3, gt_comp1_pt a ha]

theorem gt_comp_inv' {n : ℕ} {φ φi : Pt k 1 d} (h : IsInvPair φ φi) (a : Pt k n d) (ha : GP a) :
    comp1 φi (comp1 φ a) = a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [← gt_comp1_comp1 φi φ h1 a ha, h4, gt_comp1_pt a ha]

theorem gt_const_ev_eq {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d) :
    constantCoeff (ev V f) = constantCoeff f := by
  exact gt_cc_lemma (fun p : Fin m × Fin d => V p.1 p.2) (fun p => hV p.1 p.2) f

theorem gt_map_id {σ : Type} (f : MvPowerSeries σ k) : MvPowerSeries.map (algebraMap k k) f = f := by
  first
    | (ext e; simp)
    | simp

end Calc

section Calc2

variable {k : Type} [CommRing k] {d : ℕ}

theorem eval_pair_points {m n : ℕ} (V : Fin m → Pt k n d) (a b : Pt k m d) :
    (fun j => evP V (![a, b] j)) = ![evP V a, evP V b] := by
  funext j
  fin_cases j <;> rfl

private theorem gt_evz_lemma {m n : ℕ} (f : PS k m d) (hf : constantCoeff f = 0) :
    ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) f = 0 := by
  have hz : ∀ j, GP ((fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) j) := by
    intro j
    show ∀ i, _
    intro i
    simp
  have he : ∀ j, GP ((Fin.elim0 : Fin 0 → Pt k n d) j) := fun j => Fin.elim0 j
  have h1 := gt_ev_ev (Fin.elim0 : Fin 0 → Pt k n d) (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) he hz f
  have h2 : ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) f = 0 := by
    ext e
    rw [Subsingleton.elim e 0]
    simpa using gt_const_ev (fun (_ : Fin m) (_ : Fin d) => (0 : PS k 0 d)) hz f hf
  simp only [h2, gt_ev_zero _ he] at h1
  first
    | exact h1.symm
    | exact h1

theorem gt_comp1_zero {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) : comp1 φ (0 : Pt k n d) = 0 := by
  funext i
  have h0 : (![(0 : Pt k n d)] : Fin 1 → Pt k n d) = fun _ _ => 0 := by
    funext j l
    fin_cases j
    rfl
  show ev ![(0 : Pt k n d)] (φ i) = 0
  rw [h0]
  exact gt_evz_lemma (φ i) (hφ i)

theorem evP_zero {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) : evP V (0 : Pt k m d) = 0 := by
  funext i
  exact gt_ev_zero V hV

theorem gt_ev_pt_self (f : PS k 1 d) : ev ![pt k (n := 1) d 0] f = f := by
  have h : (fun p : Fin 1 × Fin d => (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) p.1 p.2) =
      MvPowerSeries.X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    rfl
  show MvPowerSeries.subst _ f = f
  first
    | (rw [h, MvPowerSeries.subst_self]; rfl)
    | rw [h, MvPowerSeries.subst_self]
    | simp [h, MvPowerSeries.subst_self]

theorem gt_comp1_pt_right (φ : Pt k 1 d) : comp1 φ (pt k (n := 1) d 0) = φ := by
  funext i
  exact gt_ev_pt_self (φ i)

end Calc2

section Main

private theorem gt_ev2_lemma {k : Type} [CommRing k] {d m n : ℕ} (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (x y : Pt k m d) (hx : GP x) (hy : GP y) (f : PS k 2 d) :
    ev V (ev ![x, y] f) = ev ![evP V x, evP V y] f := by
  rw [gt_ev_ev' V ![x, y] hV (pair_points_zero_constant hx hy) f]
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem gt_cc3_lemma {k : Type} [CommRing k] {d n : ℕ} (f : PS k 2 d) (hf : constantCoeff f = 0)
    (V1 V2 V3 : Fin 2 → Pt k n d) (h1 : ∀ j, GP (V1 j)) (h2 : ∀ j, GP (V2 j)) (h3 : ∀ j, GP (V3 j)) :
    constantCoeff (ev V1 f + ev V2 f - ev V3 f) = 0 := by
  rw [map_sub, map_add, gt_const_ev V1 h1 f hf, gt_const_ev V2 h2 f hf, gt_const_ev V3 h3 f hf]
  all_goals simp

private theorem gt_cc2_lemma {k : Type} [CommRing k] {d n : ℕ} (f : PS k 2 d) (hf : constantCoeff f = 0)
    (V1 V2 : Fin 2 → Pt k n d) (h1 : ∀ j, GP (V1 j)) (h2 : ∀ j, GP (V2 j)) :
    constantCoeff (ev V1 f - ev V2 f) = 0 := by
  rw [map_sub, gt_const_ev V1 h1 f hf, gt_const_ev V2 h2 f hf]
  all_goals simp

theorem gauge_transformation : GaugeTransSt := by
  intro k _ _ d O _ _ B B' φ φi lam hinv hl0 hl1 hF hA hp1 hp2 hsy had h hh
  obtain ⟨hφ, hφi, hc1, hc2⟩ := id hinv
  have z1 : GP (0 : Pt k 1 d) := gp_zero₂
  have q1 : GP (pt k (n := 1) d 0) := gp_pt 0
  have q2 : ∀ j : Fin 2, GP (pt k (n := 2) d j) := fun j => gp_pt j
  have q3 : ∀ j : Fin 3, GP (pt k (n := 3) d j) := fun j => gp_pt j
  have hFc : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hFc' : ∀ i, constantCoeff (B'.G.F i) = 0 := B'.G.const
  have hAc : ∀ a, GP (B.A.act a) := fun a => B.A.const a
  have hAc' : ∀ a, GP (B'.A.act a) := fun a => B'.A.const a
  have hΦ2 : ∀ j, GP ((![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1))
  have hΦ3 : ∀ j, GP ((![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] : Fin 3 → Pt k 3 d) j) :=
    triple_points_zero_constant (gp_comp1 φ _ hφ (q3 0)) (gp_comp1 φ _ hφ (q3 1)) (gp_comp1 φ _ hφ (q3 2))
  have ev20 : evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (pt k (n := 2) d 0) = comp1 φ (pt k (n := 2) d 0) := evP_pt _ hΦ2 0
  have ev21 : evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (pt k (n := 2) d 1) = comp1 φ (pt k (n := 2) d 1) := evP_pt _ hΦ2 1
  have ev30 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 0) = comp1 φ (pt k (n := 3) d 0) := evP_pt _ hΦ3 0
  have ev31 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 1) = comp1 φ (pt k (n := 3) d 1) := evP_pt _ hΦ3 1
  have ev32 : evP ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1), comp1 φ (pt k (n := 3) d 2)] (pt k (n := 3) d 2) = comp1 φ (pt k (n := 3) d 2) := evP_pt _ hΦ3 2
  have hFK : B.FK k = B.G.F := by
    funext i
    exact gt_map_id _
  have hFK' : B'.FK k = B'.G.F := by
    funext i
    exact gt_map_id _
  have hAK : ∀ a, B.actK k a = B.A.act a := fun a => by
    funext i
    exact gt_map_id _
  have hAK' : ∀ a, B'.actK k a = B'.A.act a := fun a => by
    funext i
    exact gt_map_id _
  have hh0 : constantCoeff h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant z1 q1) h, hh.ax0, map_zero]
  have hl0' : constantCoeff lam = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant z1 q1) lam, hl0, map_zero]
  have K2 : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y → ∀ f : PS k 2 d,
      ev ![x, y] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] f) = ev ![comp1 φ x, comp1 φ y] f := by
    intro m x y hx hy f
    have a0 : evP ![x, y] (pt k (n := 2) d 0) = x := evP_pt _ (pair_points_zero_constant hx hy) 0
    have a1 : evP ![x, y] (pt k (n := 2) d 1) = y := evP_pt _ (pair_points_zero_constant hx hy) 1
    rw [gt_ev2_lemma ![x, y] (pair_points_zero_constant hx hy) _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1)) f,
      evP_comp1 ![x, y] (pair_points_zero_constant hx hy) φ _ (q2 0), evP_comp1 ![x, y] (pair_points_zero_constant hx hy) φ _ (q2 1), a0, a1]
  have KH : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      ev ![x, y] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = ev ![comp1 φ x, comp1 φ y] h + ev ![x, y] lam := by
    intro m x y hx hy
    rw [gt_ev_add _ (pair_points_zero_constant hx hy), K2 x y hx hy h]
  have TI : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      addOf B'.G.F x y = comp1 φi (addOf B.G.F (comp1 φ x) (comp1 φ y)) := by
    intro m x y hx hy
    have hxy := pair_points_zero_constant hx hy
    have a0 : evP ![x, y] (pt k (n := 2) d 0) = x := evP_pt _ hxy 0
    have a1 : evP ![x, y] (pt k (n := 2) d 1) = y := evP_pt _ hxy 1
    have hA2 : GP (addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
      gp_addOf _ hFc _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1))
    have hE : evP ![x, y] (addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) =
        addOf B.G.F (comp1 φ x) (comp1 φ y) := by
      rw [evP_addOf _ hxy _ _ _ (gp_comp1 φ _ hφ (q2 0)) (gp_comp1 φ _ hφ (q2 1)),
        evP_comp1 _ hxy φ _ (q2 0), evP_comp1 _ hxy φ _ (q2 1), a0, a1]
    funext i
    show ev ![x, y] (B'.G.F i) = ev ![addOf B.G.F (comp1 φ x) (comp1 φ y)] (φi i)
    rw [hF i]
    show ev ![x, y] (ev ![addOf B.G.F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))] (φi i)) = _
    rw [gt_ev_ev' _ _ hxy (single_point_zero_constant hA2) (φi i), ← hE]
    congr 1
    funext j
    fin_cases j
    rfl
  have TI' : ∀ {m : ℕ} (x y : Pt k m d), GP x → GP y →
      comp1 φ (addOf B'.G.F x y) = addOf B.G.F (comp1 φ x) (comp1 φ y) := by
    intro m x y hx hy
    rw [TI x y hx hy]
    exact gt_comp_inv hinv _ (gp_addOf _ hFc _ _ (gp_comp1 φ x hφ hx) (gp_comp1 φ y hφ hy))
  have TA : ∀ (a : O) {m : ℕ} (x : Pt k m d), GP x →
      comp1 φ (comp1 (B'.A.act a) x) = comp1 (B.A.act a) (comp1 φ x) := by
    intro a m x hx
    rw [hA a, gt_comp1_comp1 φi _ (gp_comp1 _ φ (hAc a) hφ) x hx,
      gt_comp1_comp1 (B.A.act a) φ hφ x hx]
    exact gt_comp_inv hinv _ (gp_comp1 _ _ (hAc a) (gp_comp1 φ x hφ hx))
  have f0 : ev (n := 1) ![0, pt k (n := 1) d 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = 0 := by
    rw [gt_ev_add _ (pair_points_zero_constant z1 q1), hl0, add_zero, K2 _ _ z1 q1, gt_comp1_zero φ hφ, gt_comp1_pt_right]
    have e := congrArg (ev ![φ]) hh.ax0
    rw [gt_ev2_lemma ![φ] (single_point_zero_constant hφ) _ _ z1 q1, evP_zero ![φ] (single_point_zero_constant hφ),
      evP_pt ![φ] (single_point_zero_constant hφ), gt_ev_zero ![φ] (single_point_zero_constant hφ)] at e
    exact e
  have f1 : ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) = 0 := by
    rw [gt_ev_add _ (pair_points_zero_constant q1 z1), hl1, add_zero, K2 _ _ q1 z1, gt_comp1_zero φ hφ, gt_comp1_pt_right]
    have e := congrArg (ev ![φ]) hh.ax1
    rw [gt_ev2_lemma ![φ] (single_point_zero_constant hφ) _ _ q1 z1, evP_zero ![φ] (single_point_zero_constant hφ),
      evP_pt ![φ] (single_point_zero_constant hφ), gt_ev_zero ![φ] (single_point_zero_constant hφ)] at e
    exact e
  have gF3 : GP (addOf B.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1)) := gp_addOf _ hFc _ _ (q3 0) (q3 1)
  have gF3' : GP (addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1)) := gp_addOf _ hFc' _ _ (q3 0) (q3 1)
  have gG3 : GP (addOf B.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)) := gp_addOf _ hFc _ _ (q3 1) (q3 2)
  have gG3' : GP (addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)) := gp_addOf _ hFc' _ _ (q3 1) (q3 2)
  have e1 : B.ph1 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] h + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] h - ev (n := 3) ![addOf B.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] h) := by
    have e := hh.ph1
    rw [hFK] at e
    exact (gt_map_id _).symm.trans e
  have e2 : B.ph2 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] h + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] h - ev (n := 3) ![pt k (n := 3) d 0, addOf B.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] h) := by
    have e := hh.ph2
    rw [hFK] at e
    exact (gt_map_id _).symm.trans e
  have esy : B.sy = FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] h - h) := (gt_map_id _).symm.trans hh.sy
  have ead : ∀ a, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] h - ev (n := 2) ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] h) := by
    intro a
    have e := hh.ad a
    rw [hAK a, hAK (star a)] at e
    exact (gt_map_id _).symm.trans e
  have ccM := gt_cc3_lemma h hh0 _ _ _ (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 1) (q3 2)) (pair_points_zero_constant gF3 (q3 2))
  have ccL1 := gt_cc3_lemma lam hl0' _ _ _ (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 1) (q3 2)) (pair_points_zero_constant gF3' (q3 2))
  have ccM2 := gt_cc3_lemma h hh0 _ _ _ (pair_points_zero_constant (q3 0) (q3 1)) (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 0) gG3)
  have ccL2 := gt_cc3_lemma lam hl0' _ _ _ (pair_points_zero_constant (q3 0) (q3 1)) (pair_points_zero_constant (q3 0) (q3 2)) (pair_points_zero_constant (q3 0) gG3')
  have ccS : constantCoeff (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] h - h) = 0 := by
    rw [map_sub, gt_const_ev_eq _ (pair_points_zero_constant (q2 1) (q2 0)), sub_self]
  have ccLS : constantCoeff (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] lam - lam) = 0 := by
    rw [map_sub, gt_const_ev_eq _ (pair_points_zero_constant (q2 1) (q2 0)), sub_self]
  have f2 : B'.ph1 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 3) ![addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hp1, e1, gt_ev_expS _ hΦ3 _ ccM, ← gt_expS_add _ _ (gt_const_ev _ hΦ3 _ ccM) ccL1]
    congr 1
    rw [KH _ _ (q3 0) (q3 2), KH _ _ (q3 1) (q3 2), KH _ _ gF3' (q3 2), TI' _ _ (q3 0) (q3 1),
      gt_ev_sub _ hΦ3, gt_ev_add _ hΦ3,
      gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 2), gt_ev2_lemma _ hΦ3 _ _ (q3 1) (q3 2), gt_ev2_lemma _ hΦ3 _ _ gF3 (q3 2),
      evP_addOf _ hΦ3 _ _ _ (q3 0) (q3 1), ev30, ev31, ev32]
    ring
  have f3 : B'.ph2 = FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 3) ![pt k (n := 3) d 0, addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hp2, e2, gt_ev_expS _ hΦ3 _ ccM2, ← gt_expS_add _ _ (gt_const_ev _ hΦ3 _ ccM2) ccL2]
    congr 1
    rw [KH _ _ (q3 0) (q3 1), KH _ _ (q3 0) (q3 2), KH _ _ (q3 0) gG3', TI' _ _ (q3 1) (q3 2),
      gt_ev_sub _ hΦ3, gt_ev_add _ hΦ3,
      gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 1), gt_ev2_lemma _ hΦ3 _ _ (q3 0) (q3 2), gt_ev2_lemma _ hΦ3 _ _ (q3 0) gG3,
      evP_addOf _ hΦ3 _ _ _ (q3 1) (q3 2), ev30, ev31, ev32]
    ring
  have f4 : B'.sy = FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    rw [hsy, esy, gt_ev_expS _ hΦ2 _ ccS, ← gt_expS_add _ _ (gt_const_ev _ hΦ2 _ ccS) ccLS]
    congr 1
    rw [KH _ _ (q2 1) (q2 0), gt_ev_sub _ hΦ2, gt_ev2_lemma _ hΦ2 _ _ (q2 1) (q2 0), ev21, ev20]
    ring
  have f5 : ∀ a, B'.ad a = FB.expS k (ev (n := 2) ![comp1 (B'.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) - ev (n := 2) ![pt k (n := 2) d 0, comp1 (B'.A.act (star a)) (pt k (n := 2) d 1)] (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) := by
    intro a
    have ccA := gt_cc2_lemma h hh0 _ _ (pair_points_zero_constant (gp_comp1 _ _ (hAc a) (q2 0)) (q2 1))
      (pair_points_zero_constant (q2 0) (gp_comp1 _ _ (hAc (star a)) (q2 1)))
    have ccLA := gt_cc2_lemma lam hl0' _ _ (pair_points_zero_constant (gp_comp1 _ _ (hAc' a) (q2 0)) (q2 1))
      (pair_points_zero_constant (q2 0) (gp_comp1 _ _ (hAc' (star a)) (q2 1)))
    rw [had a, ead a, gt_ev_expS _ hΦ2 _ ccA, ← gt_expS_add _ _ (gt_const_ev _ hΦ2 _ ccA) ccLA]
    congr 1
    rw [KH _ _ (gp_comp1 _ _ (hAc' a) (q2 0)) (q2 1), KH _ _ (q2 0) (gp_comp1 _ _ (hAc' (star a)) (q2 1)),
      TA a _ (q2 0), TA (star a) _ (q2 1),
      gt_ev_sub _ hΦ2, gt_ev2_lemma _ hΦ2 _ _ (gp_comp1 _ _ (hAc a) (q2 0)) (q2 1),
      gt_ev2_lemma _ hΦ2 _ _ (q2 0) (gp_comp1 _ _ (hAc (star a)) (q2 1)),
      evP_comp1 _ hΦ2 _ _ (q2 0), evP_comp1 _ hΦ2 _ _ (q2 1), ev20, ev21]
    ring
  refine ⟨f0, f1, ?_, ?_, ?_, ?_⟩
  · rw [hFK']
    exact (gt_map_id _).trans f2
  · rw [hFK']
    exact (gt_map_id _).trans f3
  · exact (gt_map_id _).trans f4
  · intro a
    rw [hAK' a, hAK' (star a)]
    exact (gt_map_id _).trans (f5 a)

end Main

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
