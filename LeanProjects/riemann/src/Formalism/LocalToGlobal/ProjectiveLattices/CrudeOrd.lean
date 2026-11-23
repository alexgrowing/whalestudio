import Formalism.LocalToGlobal.ProjectiveLattices.CrudeBase

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {k : Type} [CommRing k] {d n : ℕ}

theorem ordGe_one_iff (f : PS k n d) : OrdGe 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    first
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using h0
  · intro h m hm
    have hm0 : m = 0 := by
      have hd : m.degree = 0 := by omega
      first
        | exact (Finsupp.degree_eq_zero_iff m).1 hd
        | exact Finsupp.degree_eq_zero_iff.1 hd
    subst hm0
    first
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using h

theorem OrdGe.mul {a b : ℕ} {f g : PS k n d} (hf : OrdGe a f) (hg : OrdGe b g) : OrdGe (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = m := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact Finset.mem_antidiagonal.mp hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by
    rw [← hp]
    first
      | exact (map_add _ _ _).symm
      | (simp only [Finsupp.degree_eq_weight_one, map_add])
      | (rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, ← Finset.sum_add_distrib]; rfl)
      | (simp only [Finsupp.degree_eq_sum, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib])
      | (unfold Finsupp.degree
         exact (Finsupp.sum_add_index' (h := fun _ (x : ℕ) => x) (fun _ => rfl) (fun _ _ _ => rfl)).symm)
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem cro_ordGe_zero (f : PS k n d) : OrdGe 0 f := by
  intro m hm
  exact absurd hm (Nat.not_lt_zero _)

theorem cro_ordGe_add {t : ℕ} {f g : PS k n d} (hf : OrdGe t f) (hg : OrdGe t g) : OrdGe t (f + g) := by
  intro m hm
  rw [map_add, hf m hm, hg m hm, add_zero]

theorem cro_ordGe_zero' (t : ℕ) : OrdGe t (0 : PS k n d) := by
  intro m _
  exact map_zero _

theorem cro_ordGe_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → PS k n d) (hf : ∀ i ∈ s, OrdGe t (f i)) :
    OrdGe t (∑ i ∈ s, f i) := by
  intro m hm
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi m hm

theorem cro_ordGe_mul_left {t : ℕ} (g : PS k n d) {f : PS k n d} (hf : OrdGe t f) : OrdGe t (g * f) := by
  have h := OrdGe.mul (cro_ordGe_zero g) hf
  rwa [zero_add] at h

theorem cro_ordGe_pderiv {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (i : Fin n × Fin d) :
    OrdGe t (pderiv k i f) := by
  intro m hm
  unfold pderiv
  show coeff m (pderivFun i f) = 0
  unfold pderivFun
  have hz : coeff (m + Finsupp.single i 1) f = 0 := hf _ (by
    have e : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      first
        | (rw [map_add, Finsupp.degree_single])
        | simp [Finsupp.degree_single]
        | (rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
           simp [Finset.sum_add_distrib, Finsupp.single_apply])
    omega)
  show coeff (m + Finsupp.single i 1) f * ((m i : k) + 1) = 0
  rw [hz, zero_mul]

theorem cro_ordGe_lin {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (b : Fin n) (v : Fin d → k) :
    OrdGe t (Lin b v f) := by
  unfold Lin
  exact cro_ordGe_sum _ _ fun j _ => cro_ordGe_mul_left _ (cro_ordGe_pderiv hf _)

theorem cro_constCoeff_ev {m : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p i, constantCoeff (a p i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have ha' : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst ha', finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff
        (e.prod fun s j => (fun p : Fin m × Fin d => a p.1 p.2) s ^ j) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s.1 s.2, zero_pow hs])
    rw [h0, smul_zero]

theorem cro_constCoeff_expS [Algebra ℚ k] (s : PS k n d) (hs : constantCoeff s = 0) :
    constantCoeff (FB.expS k s) = 1 := by
  have hs' : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst hs', finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro e he
    rw [map_pow, hs, zero_pow he, smul_zero]

theorem cro_prod_monomial {ι σ : Type} (s : Finset ι) (f : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (f i) (1 : k) : MvPowerSeries σ k) = monomial (∑ i ∈ s, f i) 1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · first
      | simp
      | simp [MvPowerSeries.monomial_zero_eq_C]
      | (rw [Finset.prod_empty, Finset.sum_empty]; rfl)
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem cro_coeff_lin (G : FGLaw k d) (i j : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) = if i = j then 1 else 0 := by
  have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (G.unit j)
  rw [MvPowerSeries.coeff_X] at hu
  have hrhs : (if Finsupp.single ((0 : Fin 1), i) 1 = Finsupp.single ((0 : Fin 1), j) 1 then (1 : k) else 0) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg]
      intro hs
      apply hij
      have h2 := congrArg (fun D : Fin 1 × Fin d →₀ ℕ => D ((0 : Fin 1), i)) hs
      simp [Finsupp.single_apply] at h2
      first
        | exact h2.symm
        | exact h2
  rw [hrhs] at hu
  rw [← hu]
  unfold ev
  have hc0 : ∀ p : Fin 2 × Fin d,
      constantCoeff ((![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) = 0 := by
    rintro ⟨p1, p2⟩
    fin_cases p1 <;> simp [pt]
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hc0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hc0 p]; exact IsNilpotent.zero)
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ (Finsupp.single ((1 : Fin 2), i) 1)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp [pt, MvPowerSeries.coeff_X]
  · intro D hD
    suffices hc : coeff (Finsupp.single ((0 : Fin 1), i) 1)
        (D.prod fun s m => (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) = 0 by
      rw [hc, smul_zero]
    by_cases hx : ∃ s ∈ D.support, s.1 = 0
    · obtain ⟨⟨s1, s2⟩, hs, hs0⟩ := hx
      have hz : (D.prod fun s m =>
          (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) = 0 := by
        rw [Finsupp.prod]
        apply Finset.prod_eq_zero hs
        simp only at hs0
        subst hs0
        simp [zero_pow (Finsupp.mem_support_iff.mp hs)]
      rw [hz, map_zero]
    · push_neg at hx
      have hprod : (D.prod fun s m =>
          (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) =
          monomial (∑ s ∈ D.support, Finsupp.single ((0 : Fin 1), s.2) (D s)) (1 : k) := by
        rw [Finsupp.prod, ← cro_prod_monomial]
        refine Finset.prod_congr rfl fun s hs => ?_
        obtain ⟨s1, s2⟩ := s
        have h1 : s1 = 1 := by
          have := hx _ hs
          fin_cases s1
          · exact absurd rfl this
          · rfl
        subst h1
        first
          | simp [pt, MvPowerSeries.X_pow_eq]
          | simp [pt, MvPowerSeries.X, MvPowerSeries.monomial_pow]
      rw [hprod, MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      apply hD
      ext ⟨s1, s2⟩
      have hev := congrArg (fun D' : Fin 1 × Fin d →₀ ℕ => D' ((0 : Fin 1), s2)) heq
      simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Prod.mk.injEq, true_and] at hev
      rw [Finset.sum_eq_single ((1 : Fin 2), s2)] at hev
      · fin_cases s1
        · have h0 : D ((0 : Fin 2), s2) = 0 := by
            by_contra hne
            exact hx _ (Finsupp.mem_support_iff.mpr hne) rfl
          simp [h0, Finsupp.single_apply]
        · simp [Finsupp.single_apply] at hev ⊢
          split_ifs at hev ⊢ <;> omega
      · intro s hs hne
        rw [if_neg]
        intro h2
        apply hne
        obtain ⟨t1, t2⟩ := s
        have := hx _ hs
        simp only at h2 this
        subst h2
        fin_cases t1
        · exact absurd rfl this
        · rfl
      · intro hnot
        have h0 : D ((1 : Fin 2), s2) = 0 := by simpa using hnot
        simp [h0]

section Word

variable (Op Op' : PS k n d → PS k n d)

theorem cro_iter (hsub : ∀ X Y, Op (X - Y) = Op X - Op Y)
    (hlow : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op X)) (hlow' : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op' X))
    (hdiff : ∀ t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op X - Op' X)) (c : ℕ) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe (c + s) X → OrdGe (c + s) Y → OrdGe (c + s + 1) (X - Y) →
      OrdGe s (Op^[c] X) ∧ OrdGe s (Op'^[c] Y) ∧ OrdGe (s + 1) (Op^[c] X - Op'^[c] Y) := by
  induction c with
  | zero =>
    intro s X Y hX hY hXY
    simp only [Function.iterate_zero_apply]
    exact ⟨by simpa using hX, by simpa using hY, by simpa using hXY⟩
  | succ c ih =>
    intro s X Y hX hY hXY
    have hX' : OrdGe (c + s + 1) X := by rwa [show c + s + 1 = c + 1 + s by omega]
    have hY' : OrdGe (c + s + 1) Y := by rwa [show c + s + 1 = c + 1 + s by omega]
    have hXY' : OrdGe (c + s + 1 + 1) (X - Y) := by rwa [show c + s + 1 + 1 = c + 1 + s + 1 by omega]
    have h1 : OrdGe (c + s) (Op X) := hlow _ _ hX'
    have h2 : OrdGe (c + s) (Op' Y) := hlow' _ _ hY'
    have h3 : OrdGe (c + s + 1) (Op X - Op' Y) := by
      have e : Op X - Op' Y = Op (X - Y) + (Op Y - Op' Y) := by
        rw [hsub]
        abel
      rw [e]
      exact cro_ordGe_add (hlow _ _ hXY') (hdiff _ _ hY')
    simp only [Function.iterate_succ_apply]
    exact ih s (Op X) (Op' Y) h1 h2 h3

end Word

theorem cro_word {ι : Type} (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (L : List ι) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe ((L.map m).sum + s) X → OrdGe ((L.map m).sum + s) Y →
      OrdGe ((L.map m).sum + s + 1) (X - Y) →
      OrdGe s (L.foldr (fun l g => (Op l)^[m l] g) X) ∧ OrdGe s (L.foldr (fun l g => (Op' l)^[m l] g) Y) ∧
      OrdGe (s + 1) (L.foldr (fun l g => (Op l)^[m l] g) X - L.foldr (fun l g => (Op' l)^[m l] g) Y) := by
  induction L with
  | nil =>
    intro s X Y hX hY hXY
    simp only [List.map_nil, List.sum_nil, List.foldr_nil, zero_add] at hX hY hXY ⊢
    exact ⟨hX, hY, hXY⟩
  | cons l L ih =>
    intro s X Y hX hY hXY
    rw [List.map_cons, List.sum_cons] at hX hY hXY
    have hX' : OrdGe ((L.map m).sum + (m l + s)) X := by
      rwa [show (L.map m).sum + (m l + s) = m l + (L.map m).sum + s by omega]
    have hY' : OrdGe ((L.map m).sum + (m l + s)) Y := by
      rwa [show (L.map m).sum + (m l + s) = m l + (L.map m).sum + s by omega]
    have hXY' : OrdGe ((L.map m).sum + (m l + s) + 1) (X - Y) := by
      rwa [show (L.map m).sum + (m l + s) + 1 = m l + (L.map m).sum + s + 1 by omega]
    obtain ⟨h1, h2, h3⟩ := ih (m l + s) X Y hX' hY' hXY'
    simp only [List.foldr_cons]
    exact cro_iter (Op l) (Op' l) (hsub l) (hlow l) (hlow' l) (hdiff l) (m l) s _ _ h1 h2 h3

theorem cro_word_const {ι : Type} [Fintype ι] (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (X Y : PS k n d)
    (hX : OrdGe m.degree X) (hY : OrdGe m.degree Y) (hXY : OrdGe (m.degree + 1) (X - Y)) :
    constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op l)^[m l] g) X) =
      constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op' l)^[m l] g) Y) := by
  have hs : ((Finset.univ : Finset ι).toList.map m).sum = m.degree := by
    have h1 : ((Finset.univ : Finset ι).toList.map m).sum = ∑ i, m i := by
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | simp [Finset.sum_map_toList]
        | simp
    rw [h1]
    first
      | exact (Finsupp.degree_eq_sum m).symm
      | (unfold Finsupp.degree; exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi).symm)
  have hX' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0) X := by rw [hs, add_zero]; exact hX
  have hY' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0) Y := by rw [hs, add_zero]; exact hY
  have hXY' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0 + 1) (X - Y) := by
    rw [hs, add_zero]; exact hXY
  obtain ⟨-, -, h⟩ := cro_word Op Op' m hsub hlow hlow' hdiff _ 0 X Y hX' hY' hXY'
  rw [zero_add, ordGe_one_iff, map_sub, sub_eq_zero] at h
  exact h

theorem cro_lin_sub (b : Fin n) (v : Fin d → k) (X Y : PS k n d) : Lin b v (X - Y) = Lin b v X - Lin b v Y := by
  unfold Lin
  simp only [map_sub, mul_sub, Finset.sum_sub_distrib]

theorem cro_dofN_sub (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (X Y : PS k n d) :
    DofN F b v (X - Y) = DofN F b v X - DofN F b v Y := by
  unfold DofN
  simp only [map_sub, mul_sub, Finset.sum_sub_distrib]

theorem cro_ordGe_dofN (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) {t : ℕ} {X : PS k n d}
    (hX : OrdGe (t + 1) X) : OrdGe t (DofN F b v X) := by
  unfold DofN
  exact cro_ordGe_sum _ _ fun j _ => cro_ordGe_mul_left _ (cro_ordGe_pderiv hX _)

theorem cro_dofN_lin (F : Fin d → PS k 2 d)
    (hF : ∀ i j, coeff (Finsupp.single ((1 : Fin 2), i) 1) (F j) = if i = j then 1 else 0)
    (b : Fin n) (v : Fin d → k) {t : ℕ} {X : PS k n d} (hX : OrdGe (t + 1) X) :
    OrdGe (t + 1) (DofN F b v X - Lin b v X) := by
  unfold DofN Lin
  rw [← Finset.sum_sub_distrib]
  refine cro_ordGe_sum _ _ fun j _ => ?_
  beta_reduce
  rw [← sub_mul]
  have key : ∀ A : PS k n d, constantCoeff A = v j →
      OrdGe (t + 1) ((A - C (v j)) * pderiv k (b, j) X) := by
    intro A hA
    have h1 : OrdGe 1 (A - C (v j)) := by
      rw [ordGe_one_iff, map_sub, hA, MvPowerSeries.constantCoeff_C, sub_self]
    have h3 := OrdGe.mul h1 (cro_ordGe_pderiv hX (b, j))
    rwa [add_comm] at h3
  apply key
  have hc : ∀ i, constantCoeff (ev ![pt k d b, 0] ((pderiv k ((1 : Fin 2), i)) (F j))) =
      if i = j then 1 else 0 := by
    intro i
    rw [cro_constCoeff_ev]
    · rw [← hF i j]
      first
        | (show coeff (0 + Finsupp.single ((1 : Fin 2), i) 1) (F j) *
              (((0 : Fin 2 × Fin d →₀ ℕ) ((1 : Fin 2), i) : k) + 1) = _
           simp)
        | (unfold pderiv
           show coeff 0 (pderivFun ((1 : Fin 2), i) (F j)) = _
           unfold pderivFun
           simp)
    · intro p l
      fin_cases p <;> simp [pt]
  rw [map_sum]
  first
    | (simp only [map_mul, MvPowerSeries.constantCoeff_C, hc]
       simp)
    | simp [hc]

theorem nabValN_eq_lin [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d)
    (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ) (f : PS k n d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (N : ℕ) (hP : ∀ a ∈ P.support, a.degree = N)
    (hf : OrdGe N f) :
    nabValN B k h w0 m f cp u P = ∑ a ∈ P.support, P.coeff a * constantCoeff (LinMon cp u a f) := by
  classical
  have hpt : ∀ {n' : ℕ} (b : Fin n') (i : Fin d), constantCoeff (pt k d b i : PS k n' d) = 0 := by
    intro n' b i; simp [pt]
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hg.ax0
    rw [cro_constCoeff_ev] at this
    · simpa using this
    · intro p i; fin_cases p
      · simp
      · exact hpt 0 i
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    unfold FB.hL
    rw [cro_constCoeff_ev, hh0]
    intro p i
    fin_cases p
    · exact hpt 0 i
    · show constantCoeff (comp1 (B.actK k w0) (pt k d 0) i) = 0
      unfold comp1
      rw [cro_constCoeff_ev]
      · simp [FB.actK, B.A.const]
      · intro p i'; fin_cases p; exact hpt 0 i'
  set g := FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) with hg_def
  have hg1 : constantCoeff g = 1 := by
    apply cro_constCoeff_expS
    rw [smul_eq_C_mul, map_mul, map_sum]
    have : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 := by
      intro b
      rw [cro_constCoeff_ev, hL0]
      intro p i; fin_cases p; exact hpt b i
    simp [this]
  have hFK : ∀ i j, coeff (Finsupp.single ((1 : Fin 2), i) 1) (B.FK k j) = if i = j then 1 else 0 := by
    intro i j
    simp only [FB.FK, FGLaw.mapF, coeff_map, cro_coeff_lin, Algebra.algebraMap_self, RingHom.id_apply]
  unfold nabValN DpolyN
  rw [map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_mul, constantCoeff_C]
  congr 1
  have hfa : OrdGe a.degree f := (hP a ha) ▸ hf
  have hfg : OrdGe a.degree (f * g) := by simpa using hfa.mul (cro_ordGe_zero g)
  have hg' : OrdGe 1 (g - 1) := (ordGe_one_iff _).2 (by rw [map_sub, hg1, map_one, sub_self])
  have hdiff : OrdGe (a.degree + 1) (f * g - f) := by
    have : f * g - f = f * (g - 1) := by ring
    rw [this]; exact hfa.mul hg'
  have s1 := cro_word_const (fun l => DofN (B.FK k) (cp l) (u l)) (fun l => Lin (cp l) (u l)) a
    (fun l X Y => cro_dofN_sub _ _ _ X Y) (fun l t X hX => cro_ordGe_dofN _ _ _ hX)
    (fun l t X hX => cro_ordGe_lin hX _ _) (fun l t X hX => cro_dofN_lin _ hFK _ _ hX) (f * g) (f * g)
    hfg hfg (by rw [sub_self]; exact cro_ordGe_zero' _)
  have s2 := cro_word_const (fun l => Lin (cp l) (u l)) (fun l => Lin (cp l) (u l)) a
    (fun l X Y => cro_lin_sub _ _ X Y) (fun l t X hX => cro_ordGe_lin hX _ _)
    (fun l t X hX => cro_ordGe_lin hX _ _) (fun l t X hX => by rw [sub_self]; exact cro_ordGe_zero' _)
    (f * g) f hfg hfa hdiff
  unfold DmonN LinMon
  exact s1.trans s2

end Formalism.L2.Pj.Crude
