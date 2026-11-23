import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero

noncomputable section

namespace PositivityTheory.HtPt.Ca

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (eXv eZ swE coeff_ev_zero_left coeff_ev_zero_right coeff_ev_swap')

variable {R : Type} [CommRing R] {d : ℕ}

theorem ZZa : ZZ (![0, pt R d 0] : Fin 2 → Pt R 1 d) := cechDeRhamTotalCocyclesTwo Z_zero (Z_pt 0)
theorem ZZb : ZZ (![pt R d 0, 0] : Fin 2 → Pt R 1 d) := cechDeRhamTotalCocyclesTwo (Z_pt 0) Z_zero
theorem ZZs : ZZ (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) := cechDeRhamTotalCocyclesTwo (Z_pt 1) (Z_pt 0)

theorem axOne_mul {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) : AxOne (f * g) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  exact ⟨by rw [ev_mul _ ZZa, hf1, hg1, one_mul], by rw [ev_mul _ ZZb, hf2, hg2, one_mul]⟩

theorem ax_left {f : PS R 2 d} (hf : AxOne f) {n : ℕ} {a : Pt R n d} (ha : Z a) : ev ![0, a] f = 1 := by
  have h := ev_ev ZZa (cechDeRhamTotalCocyclesOne ha) f
  rw [hf.1, ev_one] at h
  rw [h]
  congr 1
  funext j
  fin_cases j
  · simp [evalPoints_zero (cechDeRhamTotalCocyclesOne ha)]
  · simp [evalPoints_coordinatePoint (cechDeRhamTotalCocyclesOne ha)]

theorem ax_right {f : PS R 2 d} (hf : AxOne f) {n : ℕ} {a : Pt R n d} (ha : Z a) : ev ![a, 0] f = 1 := by
  have h := ev_ev ZZb (cechDeRhamTotalCocyclesOne ha) f
  rw [hf.2, ev_one] at h
  rw [h]
  congr 1
  funext j
  fin_cases j
  · simp [evalPoints_coordinatePoint (cechDeRhamTotalCocyclesOne ha)]
  · simp [evalPoints_zero (cechDeRhamTotalCocyclesOne ha)]

theorem bil_right (f : PS R 2 d) (m : ℕ) (i j : Fin d) :
    bil f m 1 i j = coeff (Finsupp.single ((0 : Fin 1), i) m)
      (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), j) f)) := by
  rw [coeff_ev_zero_right, Finsupp.embDomain_single]
  have h0 : (Finsupp.single (eXv d ((0 : Fin 1), i)) m) ((1 : Fin 2), j) = 0 := by
    show (Finsupp.single ((0 : Fin 2), i) m) ((1 : Fin 2), j) = 0
    simp [Finsupp.single_apply]
  rw [← coeff_add_single _ _ h0]
  rfl

theorem bil_swap (f : PS R 2 d) (m n : ℕ) :
    bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose := by
  ext i j
  simp only [bil, Matrix.transpose_apply]
  rw [coeff_ev_swap', Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm]
  rfl

theorem axOne_swap {f : PS R 2 d} (hf : AxOne f) : AxOne (ev (n := 2) ![pt R d 1, pt R d 0] f) := by
  constructor
  · rw [ev_ev ZZs ZZa]
    convert hf.2 using 2
    funext j
    fin_cases j <;> simp [evalPoints_coordinatePoint ZZa]
  · rw [ev_ev ZZs ZZb]
    convert hf.1 using 2
    funext j
    fin_cases j <;> simp [evalPoints_coordinatePoint ZZb]

theorem bil_mul_left {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) (m : ℕ) :
    bil (f * g) m 1 = bil f m 1 + bil g m 1 := by
  ext i j
  rw [Matrix.add_apply, bil_right, bil_right, bil_right, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    ev_add _ ZZb, ev_mul _ ZZb, ev_mul _ ZZb, hf.2, hg.2, one_mul, one_mul, map_add, add_comm]

theorem bil_mul_right {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) (n : ℕ) :
    bil (f * g) 1 n = bil f 1 n + bil g 1 n := by
  have key : ∀ h : PS R 2 d, bil h 1 n = (bil (ev (n := 2) ![pt R d 1, pt R d 0] h) n 1).transpose := by
    intro h
    rw [bil_swap, Matrix.transpose_transpose]
  rw [key (f * g), key f, key g, ev_mul _ ZZs, bil_mul_left (axOne_swap hf) (axOne_swap hg),
    Matrix.transpose_add]

theorem axOne_comp {f : PS R 2 d} (hf : AxOne f) {φ ψ : Pt R 1 d} (hφ : Z φ) (hψ : Z ψ) :
    AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) := by
  have ha : ZZ (![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] : Fin 2 → Pt R 2 d) :=
    cechDeRhamTotalCocyclesTwo (Z_comp1 hφ (Z_pt 0)) (Z_comp1 hψ (Z_pt 1))
  constructor
  · rw [ev_ev ha ZZa]
    convert ax_left hf (Z_comp1 hψ (Z_pt (n := 1) (d := d) (R := R) 0)) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZa, evalPoints_coordinatePoint ZZa, germComp1_zero_of_noConstantCoeff hφ, Z_pt]
  · rw [ev_ev ha ZZb]
    convert ax_right hf (Z_comp1 hφ (Z_pt (n := 1) (d := d) (R := R) 0)) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZb, evalPoints_coordinatePoint ZZb, germComp1_zero_of_noConstantCoeff hψ, Z_pt]

theorem bil_dd (f : PS R 2 d) (i j : Fin d) :
    bil f 1 1 i j = constantCoeff (pderiv R ((0 : Fin 2), i) (pderiv R ((1 : Fin 2), j) f)) := by
  show coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) f = _
  rw [coeff_add_single (Finsupp.single ((0 : Fin 2), i) 1) ((1 : Fin 2), j)
    (by simp [Finsupp.single_apply]), coeff_single_one]

theorem cc_d_ax {f : PS R 2 d} (hf : AxOne f) (p : Fin 2 × Fin d) : constantCoeff (pderiv R p f) = 0 := by
  obtain ⟨k, l⟩ := p
  rw [← coeff_single_one]
  fin_cases k
  · have h := coeff_ev_zero_right f (Finsupp.single ((0 : Fin 1), l) 1)
    rw [hf.2, Finsupp.embDomain_single, coeff_one,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)] at h
    exact h.symm
  · have h := coeff_ev_zero_left f (Finsupp.single ((0 : Fin 1), l) 1)
    rw [hf.1, Finsupp.embDomain_single, coeff_one,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)] at h
    exact h.symm

theorem bil_comp {f : PS R 2 d} (hf : AxOne f) {φ ψ : Pt R 1 d} (hφ : Z φ) (hψ : Z ψ) :
    bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 =
      (lin φ 1).transpose * bil f 1 1 * lin ψ 1 := by
  have ha : ZZ (![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] : Fin 2 → Pt R 2 d) :=
    cechDeRhamTotalCocyclesTwo (Z_comp1 hφ (Z_pt 0)) (Z_comp1 hψ (Z_pt 1))
  ext i j
  rw [bil_dd, cc_dd_ev ha _ _ f (cc_d_ax hf)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, cc_d_comp1_pt]
  simp [bil_dd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem bil_ptPow (f : PS R 2 d) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 := by
  ext i j
  have hfun : (fun p : Fin 2 × Fin d => (![ptPow R d m 0, ptPow R d n 1] : Fin 2 → Pt R 2 d) p.1 p.2)
      = fun s => X s ^ (![m, n] : Fin 2 → ℕ) s.1 := by
    funext ⟨k, l⟩
    fin_cases k <;> rfl
  show coeff (Finsupp.single ((0 : Fin 2), i) m + Finsupp.single ((1 : Fin 2), j) n)
      (subst (fun p : Fin 2 × Fin d => (![ptPow R d m 0, ptPow R d n 1] : Fin 2 → Pt R 2 d) p.1 p.2) f) =
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) f
  rw [hfun]
  apply coeff_subst_pow
  · rintro ⟨k, l⟩
    fin_cases k
    · simpa using hm
    · simpa using hn
  · rintro ⟨k, l⟩
    fin_cases k <;> simp [Finsupp.single_apply, mul_ite]

theorem bil_calc : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 := by
  intro R _ d f g φ ψ hf hg hφ hψ
  exact ⟨axOne_mul hf hg, fun m => bil_mul_left hf hg m, fun n => bil_mul_right hf hg n,
    axOne_comp hf hφ hψ, bil_comp hf hφ hψ, fun m n => bil_swap f m n,
    fun m n hm hn => bil_ptPow f hm hn⟩

theorem lin_add (G : FGLaw R d) {a b : Pt R 1 d} (ha : Z a) (hb : Z b) :
    lin (G.add a b) 1 = lin a 1 + lin b 1 := by
  have hF1 : ∀ i l, constantCoeff (pderiv R ((1 : Fin 2), l) (G.F i)) = if i = l then 1 else 0 := by
    intro i l
    have h := coeff_ev_zero_left (G.F i) (Finsupp.single ((0 : Fin 1), l) 1)
    rw [G.unit i, Finsupp.embDomain_single, coeff_X] at h
    rw [← coeff_single_one]
    refine h.symm.trans ?_
    by_cases h' : i = l
    · subst h'
      simp
    · simp [Finsupp.single_eq_single_iff, Ne.symm h', h']
  have hF0 : ∀ i l, constantCoeff (pderiv R ((0 : Fin 2), l) (G.F i)) = if i = l then 1 else 0 := by
    intro i l
    have h2 := coeff_ev_swap' (G.F i) (Finsupp.single ((0 : Fin 2), l) 1)
    rw [G.comm i, Finsupp.embDomain_single] at h2
    rw [← coeff_single_one, h2, ← hF1 i l, coeff_single_one]
    rfl
  ext i j
  simp only [Matrix.add_apply, lin, FGLaw.add, addOf]
  rw [coeff_single_one, coeff_single_one, coeff_single_one, cc_d_ev (cechDeRhamTotalCocyclesTwo ha hb),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [hF0, hF1]

variable {O : Type} [CommRing O] [StarRing O]

theorem rho_mul (B : FB R d O) (a b : O) : rho B (a * b) = rho B a * rho B b := by
  show lin (B.A.act (a * b)) 1 = lin (B.A.act a) 1 * lin (B.A.act b) 1
  rw [B.A.mul_act, lin_comp1 _ (B.A.const b)]

theorem rho_add (B : FB R d O) (a b : O) : rho B (a + b) = rho B a + rho B b := by
  show lin (B.A.act (a + b)) 1 = lin (B.A.act a) 1 + lin (B.A.act b) 1
  rw [B.A.add_act, lin_add B.G (B.A.const a) (B.A.const b)]

theorem act_zero_eq (B : FB R d O) : B.A.act 0 = 0 := by
  have hc : ∀ i, constantCoeff (B.A.act 0 i) = 0 := B.A.const 0
  have hidem : B.A.act 0 = comp1 (B.A.act 0) (B.A.act 0) := by
    rw [← B.A.mul_act, mul_zero]
  have hlin : ∀ i j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act 0 i) = 0 := by
    have h := rho_add B 0 0
    rw [add_zero] at h
    have h0 : rho B 0 = 0 := by simpa using h
    intro i j
    exact congrFun (congrFun h0 i) j
  have hdeg1 : ∀ e : Fin 1 × Fin d →₀ ℕ, Finsupp.degree e = 1 → ∃ t, e = Finsupp.single t 1 := by
    intro e he
    obtain ⟨t, ht⟩ : ∃ t, e t ≠ 0 := by
      by_contra hne
      push_neg at hne
      have : e = 0 := Finsupp.ext hne
      simp [this] at he
    refine ⟨t, ?_⟩
    have hle : Finsupp.single t 1 ≤ e := by
      intro s
      rw [Finsupp.single_apply]
      split_ifs with hs
      · subst hs
        omega
      · exact Nat.zero_le _
    have hsum := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single, he] at hsum
    have hz : Finsupp.degree (e - Finsupp.single t 1) = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff, tsub_eq_zero_iff_le] at hz
    exact le_antisymm hz hle
  have hord : ∀ i, (2 : ℕ∞) ≤ (B.A.act 0 i).order := by
    intro i
    apply MvPowerSeries.le_order
    intro e he
    have he' : Finsupp.degree e < 2 := by exact_mod_cast he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h0 | h1
    · rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h0
      subst h0
      simpa using hc i
    · obtain ⟨⟨q, j⟩, rfl⟩ := hdeg1 e h1
      have hq : q = 0 := Subsingleton.elim _ _
      subst hq
      exact hlin i j
  have hsubst : HasSubst (fun p : Fin 1 × Fin d => (![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) :=
    hasSubst_ev ![B.A.act 0] (by
      intro j l
      fin_cases j
      exact hc l)
  have hstep : ∀ i, (⨅ i, (B.A.act 0 i).order) * (⨅ i, (B.A.act 0 i).order) ≤
      (B.A.act 0 i).order := by
    intro i
    have hsub := MvPowerSeries.le_order_subst hsubst (B.A.act 0 i)
    have heq : subst (fun p : Fin 1 × Fin d => (![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2)
        (B.A.act 0 i) = B.A.act 0 i := by
      conv_rhs => rw [hidem]
      rfl
    rw [heq] at hsub
    refine le_trans ?_ hsub
    have h1 : (⨅ i, (B.A.act 0 i).order) ≤
        ⨅ p : Fin 1 × Fin d, ((![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2).order := by
      refine le_iInf fun p => ?_
      have hp : (![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 = B.A.act 0 := by
        rw [Subsingleton.elim p.1 0]
        rfl
      rw [hp]
      exact iInf_le _ p.2
    exact mul_le_mul' h1 (iInf_le _ i)
  have hkk := le_iInf hstep
  have h2k : (2 : ℕ∞) ≤ ⨅ i, (B.A.act 0 i).order := le_iInf hord
  have htop : (⨅ i, (B.A.act 0 i).order) = ⊤ := by
    by_contra hne
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at hkk h2k
    have h2n : 2 ≤ n := by exact_mod_cast h2k
    have hnn : n * n ≤ n := by exact_mod_cast hkk
    nlinarith
  funext i
  have hi : (B.A.act 0 i).order = ⊤ := by
    apply eq_top_iff.mpr
    rw [← htop]
    exact iInf_le _ i
  exact MvPowerSeries.order_eq_top_iff.mp hi

theorem eval3_axiom_zero {f : PS R 3 d} (hf : ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1) {n : ℕ} {a b : Pt R n d}
    (ha : Z a) (hb : Z b) : ev ![0, a, b] f = 1 := by
  have h := ev_ev (zero_constant_triple Z_zero (Z_pt 0) (Z_pt 1) :
    ZZ (![0, pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d)) (cechDeRhamTotalCocyclesTwo ha hb) f
  rw [hf, ev_one] at h
  rw [h]
  congr 1
  funext j
  fin_cases j <;> simp [evalPoints_zero (cechDeRhamTotalCocyclesTwo ha hb), evalPoints_coordinatePoint (cechDeRhamTotalCocyclesTwo ha hb)]

theorem eval3_axiom_one {f : PS R 3 d} (hf : ev (n := 2) ![pt R d 0, 0, pt R d 1] f = 1) {n : ℕ} {a b : Pt R n d}
    (ha : Z a) (hb : Z b) : ev ![a, 0, b] f = 1 := by
  have h := ev_ev (zero_constant_triple (Z_pt 0) Z_zero (Z_pt 1) :
    ZZ (![pt R d 0, 0, pt R d 1] : Fin 3 → Pt R 2 d)) (cechDeRhamTotalCocyclesTwo ha hb) f
  rw [hf, ev_one] at h
  rw [h]
  congr 1
  funext j
  fin_cases j <;> simp [evalPoints_zero (cechDeRhamTotalCocyclesTwo ha hb), evalPoints_coordinatePoint (cechDeRhamTotalCocyclesTwo ha hb)]

theorem eval3_axiom_two {f : PS R 3 d} (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) {n : ℕ} {a b : Pt R n d}
    (ha : Z a) (hb : Z b) : ev ![a, b, 0] f = 1 := by
  have h := ev_ev (zero_constant_triple (Z_pt 0) (Z_pt 1) Z_zero :
    ZZ (![pt R d 0, pt R d 1, 0] : Fin 3 → Pt R 2 d)) (cechDeRhamTotalCocyclesTwo ha hb) f
  rw [hf, ev_one] at h
  rw [h]
  congr 1
  funext j
  fin_cases j <;> simp [evalPoints_zero (cechDeRhamTotalCocyclesTwo ha hb), evalPoints_coordinatePoint (cechDeRhamTotalCocyclesTwo ha hb)]

def Ax3 (f : PS R 3 d) : Prop := ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1 ∧
  ev (n := 2) ![pt R d 0, 0, pt R d 1] f = 1 ∧ ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1

theorem axOne_xxz {f : PS R 3 d} (hf : Ax3 f) {φ ψ : Pt R 1 d} (hφ : Z φ) (hψ : Z ψ) :
    AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 0), pt R d 1] f) := by
  have ha : ZZ (![comp1 φ (pt R d 0), comp1 ψ (pt R d 0), pt R d 1] : Fin 3 → Pt R 2 d) :=
    zero_constant_triple (Z_comp1 hφ (Z_pt 0)) (Z_comp1 hψ (Z_pt 0)) (Z_pt 1)
  constructor
  · rw [ev_ev ha ZZa]
    convert eval3_axiom_zero hf.1 (Z_zero (n := 1)) (Z_pt (R := R) (d := d) (n := 1) 0) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZa, evalPoints_coordinatePoint ZZa, germComp1_zero_of_noConstantCoeff hφ, germComp1_zero_of_noConstantCoeff hψ, Z_pt]
  · rw [ev_ev ha ZZb]
    convert eval3_axiom_two hf.2.2 (Z_comp1 hφ (Z_pt (R := R) (d := d) (n := 1) 0))
      (Z_comp1 hψ (Z_pt (R := R) (d := d) (n := 1) 0)) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZb, evalPoints_coordinatePoint ZZb, Z_pt]

theorem axOne_xzz {f : PS R 3 d} (hf : Ax3 f) {φ ψ : Pt R 1 d} (hφ : Z φ) (hψ : Z ψ) :
    AxOne (ev (n := 2) ![pt R d 0, comp1 φ (pt R d 1), comp1 ψ (pt R d 1)] f) := by
  have ha : ZZ (![pt R d 0, comp1 φ (pt R d 1), comp1 ψ (pt R d 1)] : Fin 3 → Pt R 2 d) :=
    zero_constant_triple (Z_pt 0) (Z_comp1 hφ (Z_pt 1)) (Z_comp1 hψ (Z_pt 1))
  constructor
  · rw [ev_ev ha ZZa]
    convert eval3_axiom_zero hf.1 (Z_comp1 hφ (Z_pt (R := R) (d := d) (n := 1) 0))
      (Z_comp1 hψ (Z_pt (R := R) (d := d) (n := 1) 0)) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZa, evalPoints_coordinatePoint ZZa, Z_pt]
  · rw [ev_ev ha ZZb]
    convert eval3_axiom_one hf.2.1 (Z_pt (R := R) (d := d) (n := 1) 0) (Z_zero (n := 1)) using 2
    funext j
    fin_cases j <;> simp [evalPoints_comp ZZb, evalPoints_coordinatePoint ZZb, germComp1_zero_of_noConstantCoeff hφ, germComp1_zero_of_noConstantCoeff hψ, Z_pt]

theorem ax3_ph1 (B : FB R d O) : Ax3 B.ph1 := ⟨B.cocycleLeft_zero_fst, B.cocycleLeft_zero_snd, B.cocycleLeft_zero_thd⟩
theorem ax3_ph2 (B : FB R d O) : Ax3 B.ph2 := ⟨B.cocycleRight_zero_fst, B.cocycleRight_zero_snd, B.cocycleRight_zero_thd⟩

theorem comp1_identity_left {n : ℕ} (j : Fin n) : comp1 (pt R d 0) (pt R d j) = pt R d j := germ_comp1_zero_point_left _ (Z_pt j)

theorem axOne_prod {ι : Type} (s : Finset ι) (f : ι → PS R 2 d) (h : ∀ i, AxOne (f i)) : AxOne (∏ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact ⟨ev_one _, ev_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    exact axOne_mul (h a) ih

theorem act_zero : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) := by
  intro R _ d O _ _ B
  refine ⟨act_zero_eq B, fun n => ?_, fun a b => ?_, fun n => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_succ, B.A.add_act, B.A.one_act]
  · rw [← B.A.mul_act, ← B.A.mul_act, mul_comm]
  · unfold GlobalTheory.CompanionTheory.Ar.Conj.pow1
    apply axOne_prod
    intro k
    have hφ : Z (B.A.act (k : O)) := B.A.const _
    have ha : ZZ (![comp1 (B.A.act (k : O)) (pt R d 0), pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) :=
      zero_constant_triple (Z_comp1 hφ (Z_pt 0)) (Z_pt 0) (Z_pt 1)
    constructor
    · rw [ev_ev ha ZZa]
      convert eval3_axiom_zero B.cocycleLeft_zero_fst (Z_zero (n := 1)) (Z_pt (R := R) (d := d) (n := 1) 0) using 2
      funext j
      fin_cases j <;> simp [evalPoints_comp ZZa, evalPoints_coordinatePoint ZZa, germComp1_zero_of_noConstantCoeff hφ, Z_pt]
    · rw [ev_ev ha ZZb]
      convert eval3_axiom_two B.cocycleLeft_zero_thd (Z_comp1 hφ (Z_pt (R := R) (d := d) (n := 1) 0))
        (Z_pt (R := R) (d := d) (n := 1) 0) using 2
      funext j
      fin_cases j <;> simp [evalPoints_comp ZZb, evalPoints_coordinatePoint ZZb, Z_pt]
  · unfold GlobalTheory.CompanionTheory.Ar.Conj.pow2
    apply axOne_prod
    intro k
    have hφ : Z (B.A.act (k : O)) := B.A.const _
    have ha : ZZ (![pt R d 0, comp1 (B.A.act (k : O)) (pt R d 1), pt R d 1] : Fin 3 → Pt R 2 d) :=
      zero_constant_triple (Z_pt 0) (Z_comp1 hφ (Z_pt 1)) (Z_pt 1)
    constructor
    · rw [ev_ev ha ZZa]
      convert eval3_axiom_zero B.cocycleRight_zero_fst (Z_comp1 hφ (Z_pt (R := R) (d := d) (n := 1) 0))
        (Z_pt (R := R) (d := d) (n := 1) 0) using 2
      funext j
      fin_cases j <;> simp [evalPoints_comp ZZa, evalPoints_coordinatePoint ZZa, Z_pt]
    · rw [ev_ev ha ZZb]
      convert eval3_axiom_one B.cocycleRight_zero_snd (Z_pt (R := R) (d := d) (n := 1) 0) (Z_zero (n := 1)) using 2
      funext j
      fin_cases j <;> simp [evalPoints_comp ZZb, evalPoints_coordinatePoint ZZb, germComp1_zero_of_noConstantCoeff hφ, Z_pt]

end PositivityTheory.HtPt.Ca
