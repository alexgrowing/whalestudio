import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def appr (L : ℝ) (d : ℕ) (W : Ideal (MRing ι)) (a : K → ℕ) : ℝ :=
  L * (geoNum d W (fun _ k => (a k : ℤ)) : ℝ) / d.factorial

def HAsymp (L : ℝ) (d : ℕ) (W : Ideal (MRing ι)) : Prop :=
  ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
    |lg W a - appr L d W a| ≤ C * d * ((tdeg a : ℝ) + 1) ^ (d - 1)

theorem appr_shift (L : ℝ) (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt m V) (c : K → ℕ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ a : K → ℕ, (∀ k, c k ≤ a k) →
      |appr L m V a - appr L m V (a - c)| ≤ K' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  refine ⟨|L| / m.factorial * coefB m V * tdeg c * (1 + tdeg c) ^ (m - 1), ?_, fun a hca => ?_⟩
  · have := coefB_nonneg m V
    positivity
  have h := geoNum_shift_est m V hS (fun k => (a k : ℤ)) (fun k => (c k : ℤ))
  have e : (fun _ : Fin m => (fun k => (a k : ℤ)) - fun k => (c k : ℤ)) =
      fun _ k => ((a - c) k : ℤ) := by
    funext _ k
    simp [Nat.cast_sub (hca k)]
  rw [e, nrm_natCast, nrm_natCast] at h
  have hd : appr L m V a - appr L m V (a - c) = L / m.factorial *
      ((geoNum m V (fun _ k => (a k : ℤ)) : ℝ) - geoNum m V (fun _ k => ((a - c) k : ℤ))) := by
    simp only [appr]; ring
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hB := coefB_nonneg m V
  have hT : (0 : ℝ) ≤ tdeg c := by positivity
  have hN : (0 : ℝ) ≤ tdeg a := by positivity
  rw [hd, abs_mul, abs_div, abs_of_pos hf]
  calc |L| / m.factorial * |(geoNum m V (fun _ k => (a k : ℤ)) : ℝ) -
        geoNum m V (fun _ k => ((a - c) k : ℤ))|
      ≤ |L| / m.factorial * (coefB m V * (m * tdeg c * (tdeg a + 1 + tdeg c) ^ (m - 1))) := by
        gcongr
    _ ≤ |L| / m.factorial * (coefB m V * (m * tdeg c * ((1 + tdeg c) * (tdeg a + 1)) ^ (m - 1))) := by
        gcongr
        nlinarith
    _ = |L| / m.factorial * coefB m V * tdeg c * (1 + tdeg c) ^ (m - 1) * m *
          ((tdeg a : ℝ) + 1) ^ (m - 1) := by
        rw [mul_pow]; ring

theorem dim_of_minimal {W : Ideal (MRing ι)} [W.IsPrime] {s : MRing ι} (hsW : s ∉ W)
    {W' : Ideal (MRing ι)} (hW' : W' ∈ (W ⊔ Ideal.span {s}).minimalPrimes) {m : ℕ}
    (hd : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have h1 := dim_quot_minimal_add_one W W' s hsW hW'
  rw [hd, show m + 1 + Fintype.card K = (m + Fintype.card K) + 1 by omega] at h1
  exact withBot_eq_of_add_one h1

theorem le_of_tdeg_le {c a : K → ℕ} {a₀ : ℕ} (ha : ∀ k, a₀ + tdeg c ≤ a k) (k : K) :
    c k ≤ a k ∧ a₀ ≤ (a - c) k := by
  have hck : c k ≤ tdeg c := by
    unfold tdeg
    exact Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
  have hak := ha k
  refine ⟨by omega, ?_⟩
  show a₀ ≤ a k - c k
  omega

open Classical in

theorem per_factor {L : ℝ} {m p : ℕ} (hp : p.Prime) {W : Ideal (MRing ι)} [hWp : W.IsPrime]
    (hWm : IsMultiHomogIdeal W) (hpW : (p : MRing ι) ∈ W)
    (hdim : ringKrullDim (MRing ι ⧸ W) = ((m + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {cs : K → ℕ} (hs : IsMultiHomog s cs) (hsW : s ∉ W)
    (IH : ∀ W' : Ideal (MRing ι), IsMultiProjPrime W' → (p : MRing ι) ∈ W' →
      ringKrullDim (MRing ι ⧸ W') = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) →
      HAsymp L m W' ∧ SymmAt m W')
    {q : Ideal (MRing ι)} (hq : q.IsPrime) (hqm : IsMultiHomogIdeal q)
    (hJq : W ⊔ Ideal.span {s} ≤ q) (c : K → ℕ) :
    ∃ (a₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |lg q (a - c) - (if q ∈ divSupp W s then appr L m q a else 0)| ≤
        C * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
  classical
  have hpq : (p : MRing ι) ∈ q := hJq (Ideal.mem_sup_left hpW)
  by_cases hrel : IsRelevant q
  swap
  · have hnot : q ∉ divSupp W s := fun h => hrel h.2
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    refine ⟨1 + tdeg c, 0, le_rfl, fun a ha => ?_⟩
    have hpos : 0 < (a - c) k := (le_of_tdeg_le ha k).2
    rw [if_neg hnot, lg, card_mPiece_irrel hk hpos]
    simp
  by_cases hmin : q ∈ divSupp W s
  · have hqd := dim_of_minimal hsW hmin.1 hdim
    obtain ⟨⟨a₀', C', hC', hIH⟩, hS⟩ := IH q ⟨hq, hqm, hrel⟩ hpq hqd
    obtain ⟨K', hK', hsh⟩ := appr_shift L m q hS c
    refine ⟨a₀' + tdeg c, C' + K', by positivity, fun a ha => ?_⟩
    rw [if_pos hmin]
    have h1 := hIH (a - c) fun k => (le_of_tdeg_le ha k).2
    have h2 := hsh a fun k => (le_of_tdeg_le ha k).1
    have hmono := pow_tdeg_mono (tdeg_sub_le a c) (m - 1)
    have hm : (0 : ℝ) ≤ m := by positivity
    calc |lg q (a - c) - appr L m q a|
        ≤ |lg q (a - c) - appr L m q (a - c)| + |appr L m q a - appr L m q (a - c)| := by
          rw [abs_sub_comm (appr L m q a)]
          exact abs_sub_le _ _ _
      _ ≤ C' * m * ((tdeg (a - c) : ℝ) + 1) ^ (m - 1) + K' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) :=
          add_le_add h1 h2
      _ ≤ C' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) + K' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
          gcongr
      _ = (C' + K') * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by ring
  · have hnmin : q ∉ (W ⊔ Ideal.span {s}).minimalPrimes := fun h => hmin ⟨h, hrel⟩
    obtain ⟨W', hW', hW'q⟩ := Ideal.exists_minimalPrimes_le hJq
    have hne : W' ≠ q := fun h => hnmin (h ▸ hW')
    have hW'p : W'.IsPrime := hW'.1.1
    have hW'rel : IsRelevant W' := fun k => by
      obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h => hi (hW'q h)⟩
    have hW'm : IsMultiHomogIdeal W' := isMultiHomogIdeal_of_mem_minimalPrimes hWm hs hW'
    have hpW' : (p : MRing ι) ∈ W' := hW'.1.2 (Ideal.mem_sup_left hpW)
    have hW'd := dim_of_minimal hsW hW' hdim
    obtain ⟨⟨a₀', C', hC', hIH⟩, hS⟩ := IH W' ⟨hW'p, hW'm, hW'rel⟩ hpW' hW'd
    obtain ⟨S, hS', hqS⟩ := hqm
    have hex : ∃ g ∈ S, g ∉ W' := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      apply hne
      refine le_antisymm hW'q ?_
      rw [hqS]
      exact Ideal.span_le.mpr h
    obtain ⟨g, hgS, hgW'⟩ := hex
    obtain ⟨c', hgc'⟩ := hS' g hgS
    have hgq : g ∈ q := hqS ▸ Ideal.subset_span hgS
    obtain ⟨K', hK', hsh⟩ := appr_shift L m W' hS c'
    refine ⟨a₀' + tdeg c' + tdeg c, 2 * C' + K', by positivity, fun a ha => ?_⟩
    rw [if_neg hmin, sub_zero, abs_of_nonneg (lg_nonneg _ _)]
    set x := a - c with hxdef
    have hx : ∀ k, c' k ≤ x k ∧ a₀' ≤ (x - c') k := fun k =>
      le_of_tdeg_le (fun k => (le_of_tdeg_le ha k).2) k
    have hmono : lg q x ≤ lg (W' ⊔ Ideal.span {g}) x := by
      have hfin := finite_mPiece (W' ⊔ Ideal.span {g}) x hp.pos (Ideal.mem_sup_left hpW')
      have hle : W' ⊔ Ideal.span {g} ≤ q :=
        sup_le hW'q ((Ideal.span_singleton_le_iff_mem _).mpr hgq)
      have := card_mPiece_mono hle x
      unfold lg
      exact Real.log_le_log (by exact_mod_cast card_mPiece_pos q x hp.pos hpq)
        (by exact_mod_cast this)
    have hstep := lg_step hW'm hgc' (q := W')
      (fun g' => ⟨fun h => W'.mul_mem_right _ h, fun h => (hW'p.mem_or_mem h).resolve_right hgW'⟩)
      (a := x) (fun k => (hx k).1) hp.pos hpW'
    have hx0 : ∀ k, a₀' ≤ x k := fun k => le_trans (hx k).2 (Nat.sub_le _ _)
    have h1 := hIH x hx0
    have h2 := hIH (x - c') fun k => (hx k).2
    have h3 := hsh x fun k => (hx k).1
    have hm1 := pow_tdeg_mono (tdeg_sub_le a c) (m - 1)
    have hm2 := pow_tdeg_mono ((tdeg_sub_le x c').trans (tdeg_sub_le a c)) (m - 1)
    have hm : (0 : ℝ) ≤ m := by positivity
    have e1 := le_abs_self (lg W' x - appr L m W' x)
    have e2 := le_abs_self (appr L m W' x - appr L m W' (x - c'))
    have e3 := neg_abs_le (lg W' (x - c') - appr L m W' (x - c'))
    have b1 : C' * m * ((tdeg x : ℝ) + 1) ^ (m - 1) ≤ C' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      gcongr
    have b2 : C' * m * ((tdeg (x - c') : ℝ) + 1) ^ (m - 1) ≤ C' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      gcongr
    have b3 : K' * m * ((tdeg x : ℝ) + 1) ^ (m - 1) ≤ K' * m * ((tdeg a : ℝ) + 1) ^ (m - 1) := by
      gcongr
    nlinarith

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
