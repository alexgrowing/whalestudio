import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem coeff_subst_killCompl {σ τ R : Type*} [CommRing R] [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ R)
    (a : τ → MvPowerSeries σ R) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (embDomain e x) f := by
  classical
  have haS : HasSubst a := by
    apply hasSubst_of_constantCoeff_zero
    intro t
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hterm : ∀ n : τ →₀ ℕ, coeff n f • coeff x (n.prod fun s m => a s ^ m) =
      if n = embDomain e x then coeff n f else 0 := by
    intro n
    have hprod : (n.prod fun s m => a s ^ m) = killCompl e (monomial n (1 : R)) := by
      have h1 := monomial_eq (R := R) n (fun _ => 1)
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [h1, map_prod]
      simp only [map_pow, ha, Finsupp.prod]
    rw [hprod, coeff_killCompl, coeff_monomial]
    by_cases hn : n = embDomain e x
    · subst hn
      simp
    · rw [if_neg (Ne.symm hn), if_neg hn, smul_zero]
  rw [coeff_subst haS, finsum_eq_single _ (embDomain e x)]
  · rw [hterm, if_pos rfl]
  · intro n hn
    rw [hterm, if_neg hn]

variable {k : Type} [CommRing k] {d : ℕ}

def eZ (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

def eXv (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (0, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

theorem coeff_ev_zero_left (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![0, pt k d 0] h) = coeff (embDomain (eZ d) x) h := by
  have hnr : ∀ i : Fin d, ((0 : Fin 2), i) ∉ Set.range (eZ d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (1 : Fin 2) = 0 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eZ d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show (0 : PS k 1 d) = killCompl (eZ d) (X ((0 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, if_neg]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((0 : Fin 2), i)) hm
      rw [Finsupp.embDomain_notin_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1
  · show X ((0 : Fin 1), i) = killCompl (eZ d) (X ((1 : Fin 2), i))
    exact (killCompl_X (e := eZ d) ((0 : Fin 1), i)).symm

theorem coeff_ev_zero_right (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![pt k d 0, 0] h) = coeff (embDomain (eXv d) x) h := by
  have hnr : ∀ i : Fin d, ((1 : Fin 2), i) ∉ Set.range (eXv d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (0 : Fin 2) = 1 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eXv d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show X ((0 : Fin 1), i) = killCompl (eXv d) (X ((0 : Fin 2), i))
    exact (killCompl_X (e := eXv d) ((0 : Fin 1), i)).symm
  · show (0 : PS k 1 d) = killCompl (eXv d) (X ((1 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, if_neg]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((1 : Fin 2), i)) hm
      rw [Finsupp.embDomain_notin_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1

def swE (d : ℕ) : Fin 2 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (Fin.rev p.1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq, Fin.rev_inj] at h
  exact Prod.ext h.1 h.2⟩

theorem ev_swap_eq (h : PS k 2 d) : ev (n := 2) ![pt k d 1, pt k d 0] h = rename (swE d) h := by
  rw [rename_eq_subst]
  show subst (fun p : Fin 2 × Fin d => (![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) p.1 p.2) h = _
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  fin_cases a <;> rfl

theorem coeff_ev_swap (h : PS k 2 d) (x : Fin 2 × Fin d →₀ ℕ) :
    coeff (embDomain (swE d) x) (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff x h := by
  rw [ev_swap_eq, ← coeff_killCompl]
  rw [show killCompl (swE d) (rename (swE d) h) = h from DFunLike.congr_fun killCompl_comp_rename h]

theorem coeff_eq_zero_of_vanish_first_axis (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (0, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eZ d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact absurd (hm b) hab
    · exact ⟨(0, b), rfl⟩
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_left, hax]
  simp

theorem coeff_eq_zero_of_vanish_second_axis (h : PS k 2 d) (hax : ev (n := 1) ![pt k d 0, 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (1, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eXv d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact ⟨(0, b), rfl⟩
    · exact absurd (hm b) hab
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_right, hax]
  simp

theorem two_le_degree {m : Fin 2 × Fin d →₀ ℕ} {i i' : Fin d} (h0 : m (0, i) ≠ 0) (h1 : m (1, i') ≠ 0) :
    2 ≤ m.degree := by
  classical
  have hne : ((0 : Fin 2), i) ≠ ((1 : Fin 2), i') := by simp
  have hs : ({((0 : Fin 2), i), ((1 : Fin 2), i')} : Finset (Fin 2 × Fin d)) ⊆ m.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have h2 : m (0, i) + m (1, i') ≤ ∑ x ∈ m.support, m x := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset hs
  have hdeg : m.degree = ∑ x ∈ m.support, m x := by
    unfold Finsupp.degree
    rfl
  omega

theorem coeff_eq_zero_of_axes (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) : coeff m h = 0 := by
  by_cases hA : ∀ i, m (0, i) = 0
  · exact coeff_eq_zero_of_vanish_first_axis h h0 m hA
  by_cases hB : ∀ i, m (1, i) = 0
  · exact coeff_eq_zero_of_vanish_second_axis h h1 m hB
  push_neg at hA hB
  obtain ⟨i, hi⟩ := hA
  obtain ⟨i', hi'⟩ := hB
  have := two_le_degree hi hi'
  omega

theorem gaugeBilinearTerm_eq_neg_double_sum (h : PS k 2 d) (i j : Fin d) :
    sg1 k h i j = -coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) h := by
  show coeff (single ((0 : Fin 1), j) 1) (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) = _
  rw [map_neg, coeff_ev_zero_right, Finsupp.embDomain_single, coeff_pderiv]
  have he : eXv d ((0 : Fin 1), j) = ((0 : Fin 2), j) := rfl
  rw [he]
  simp [Finsupp.single_apply]

theorem swE_swE (t : Fin 2 × Fin d) : swE d (swE d t) = t := by
  obtain ⟨a, b⟩ := t
  show (Fin.rev (Fin.rev a), b) = (a, b)
  rw [Fin.rev_rev]

theorem embDomain_swE_apply (m : Fin 2 × Fin d →₀ ℕ) (t : Fin 2 × Fin d) :
    embDomain (swE d) m (swE d t) = m t := by
  simp

theorem coeff_ev_swap' (h : PS k 2 d) (m : Fin 2 × Fin d →₀ ℕ) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff (embDomain (swE d) m) h := by
  have hm : embDomain (swE d) (embDomain (swE d) m) = m := by
    ext t
    conv_lhs => rw [← swE_swE t]
    rw [embDomain_swE_apply, embDomain_swE_apply]
  have := coeff_ev_swap h (embDomain (swE d) m)
  rw [hm] at this
  exact this

theorem coeff_swap_sub_low (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h - h) = 0 := by
  have hdeg : (embDomain (swE d) m).degree = m.degree := by
    show ∑ i ∈ (embDomain (swE d) m).support, (embDomain (swE d) m) i = ∑ i ∈ m.support, m i
    rw [Finsupp.support_embDomain, Finset.sum_map]
    exact Finset.sum_congr rfl (fun x _ => embDomain_swE_apply m x)
  rw [map_sub, coeff_ev_swap', coeff_eq_zero_of_axes h h0 h1 _ (by rw [hdeg]; exact hm),
    coeff_eq_zero_of_axes h h0 h1 m hm, sub_zero]

section Exp

variable [Algebra ℚ k]

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {n : ℕ} (f g : PS k n d)
    (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (hg : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m g = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (f * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add]
  by_cases h1 : p.1.degree < 2
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem coeff_mul_eq_zero_of_left_vanishes_degree_le_two {n : ℕ} (F g : PS k n d)
    (hF : ∀ m : Fin n × Fin d →₀ ℕ, m.degree ≤ 2 → coeff m F = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree ≤ 2) : coeff m (F * g) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← hp, map_add]
  rw [hF _ (by omega), zero_mul]

theorem coeff_expS_two {n : ℕ} (f : PS k n d) (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree = 2) : coeff m (FB.expS k f) = coeff m f := by
  classical
  have haS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero
    (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf 0 (by simp))
  show coeff m (PowerSeries.subst f (PowerSeries.exp k)) = _
  rw [PowerSeries.coeff_subst haS, finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    rcases j with _ | _ | j
    · have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hm
      simp [hm0, coeff_one]
    · exact absurd rfl hj
    · rw [show f ^ (j + 2) = f * f * f ^ j by ring,
        coeff_mul_eq_zero_of_left_vanishes_degree_le_two (f * f) _ (fun q hq => coeff_mul_eq_zero_of_order_two_of_degree_le_two f f hf hf q hq) m hm.le,
        smul_zero]

end Exp

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
