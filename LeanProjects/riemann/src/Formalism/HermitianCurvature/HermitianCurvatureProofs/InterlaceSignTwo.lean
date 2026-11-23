import Formalism.HermitianCurvature.StatementM

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx3

theorem rho_eq (P : Par) (π : Ty P) (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.k - 1) :
    rho P π i = P.lo i + (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := by
  simp only [rho, dif_pos h]

theorem tyInterlaces : TyInterlaces := by
  intro P hP π i hi
  have h := Finset.mem_Icc.1 hi
  have hg := hP.gap i hi
  rw [rho_eq P π i h]
  have hb : ((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid i := by
    have := (π ⟨i - 1, by omega⟩).2
    have e : i - 1 + 1 = i := by omega
    simp only [e] at this
    omega
  have hw : (P.wid i : ℝ) ≤ P.hi i - P.lo i := Nat.floor_le (by linarith)
  have hb' : (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.wid i := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  have a1 : P.hi i ≤ P.u i - 1 / 2 := by unfold Par.hi; linarith [min_le_left (P.u i) (P.u' i)]
  have a2 : P.hi i ≤ P.u' i - 1 / 2 := by unfold Par.hi; linarith [min_le_right (P.u i) (P.u' i)]
  have a3 : P.u (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1))]
  have a4 : P.u' (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rhoUp : RhoUp := by
  intro P l π π' hU i hi
  have h := Finset.mem_Icc.1 hi
  rw [rho_eq P π i h, rho_eq P π' i h, hU ⟨i - 1, by omega⟩]
  have e : i - 1 + 1 = i := by omega
  simp only [e]
  split_ifs <;> push_cast <;> ring

theorem mono (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ d i, 1 ≤ i → i + d ≤ k → u (i + d) ≤ u i ∧ u' (i + d) ≤ u' i := by
  intro d
  induction d with
  | zero => intro i _ _; simp
  | succ d ih =>
    intro i h1 h2
    have a := ih i h1 (by omega)
    have b := h (i + d) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have e : i + (d + 1) = i + d + 1 := by ring
    rw [e]
    constructor <;> linarith [b.1, b.2.1, b.2.2.1, b.2.2.2]

theorem val_congr (P : Par) (π : Ty P) (a b : Fin (P.k - 1)) (h : a = b) :
    ((π a : Fin _) : ℕ) = ((π b : Fin _) : ℕ) := by subst h; rfl

theorem lo_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.lo i - P.u 1 - 1 / 2 = n := by
  have h := Finset.mem_Icc.1 hi
  obtain ⟨a, ha⟩ := hP.int_u (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨b, hb⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  unfold Par.lo
  rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with h | h
  · exact ⟨a, by rw [h]; linarith⟩
  · exact ⟨b, by rw [h]; linarith⟩

theorem hi_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.hi i - P.u 1 + 1 / 2 = n := by
  have h := Finset.mem_Icc.1 hi
  obtain ⟨a, ha⟩ := hP.int_u i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨b, hb⟩ := hP.int_u' i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  unfold Par.hi
  rcases min_choice (P.u i) (P.u' i) with h | h
  · exact ⟨a, by rw [h]; linarith⟩
  · exact ⟨b, by rw [h]; linarith⟩

theorem floor_of_int (x : ℝ) (h0 : 0 ≤ x) (z : ℤ) (hz : x = z) : ((⌊x⌋₊ : ℕ) : ℝ) = x := by
  have hz0 : 0 ≤ z := by have : (0 : ℝ) ≤ (z : ℝ) := hz ▸ h0; exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [hz]; simp

theorem wid_eq (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : (P.wid i : ℝ) = P.hi i - P.lo i := by
  obtain ⟨a, ha⟩ := lo_int P hP i hi
  obtain ⟨b, hb⟩ := hi_int P hP i hi
  exact floor_of_int _ (by linarith [hP.gap i hi]) (b - a - 1) (by push_cast; linarith)

theorem tyComplete : TyComplete := by
  intro P hP
  constructor
  · intro ρ hI hint
    have key : ∀ i ∈ Icc 1 (P.k - 1), 0 ≤ ρ i - P.lo i ∧ ρ i - P.lo i ≤ P.hi i - P.lo i ∧
        ((⌊ρ i - P.lo i⌋₊ : ℕ) : ℝ) = ρ i - P.lo i := by
      intro i hi
      have b := hI i hi
      have c1 : P.lo i ≤ ρ i := by
        unfold Par.lo
        have : max (P.u (i + 1)) (P.u' (i + 1)) ≤ ρ i - 1 / 2 := max_le (by linarith [b.2.2.1]) (by linarith [b.2.2.2])
        linarith
      have c2 : ρ i ≤ P.hi i := by
        unfold Par.hi
        have := le_min (a := P.u i) (b := P.u' i) (c := ρ i + 1 / 2) b.1 b.2.1
        linarith
      obtain ⟨a, ha⟩ := lo_int P hP i hi
      obtain ⟨n, hn⟩ := hint i hi
      exact ⟨by linarith, by linarith, floor_of_int _ (by linarith) (n - a) (by push_cast; linarith)⟩
    refine ⟨fun i => ⟨⌊ρ ((i : ℕ) + 1) - P.lo ((i : ℕ) + 1)⌋₊, ?_⟩, ?_⟩
    · have hi : (i : ℕ) + 1 ∈ Icc 1 (P.k - 1) := Finset.mem_Icc.2 ⟨by omega, by have := i.2; omega⟩
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (key _ hi).2.1)
    · intro i hi
      have h := Finset.mem_Icc.1 hi
      rw [rho_eq P _ i h]
      have e : i - 1 + 1 = i := by omega
      simp only [e]
      rw [(key i hi).2.2]; ring
  · intro π π' h
    funext i
    apply Fin.ext
    have hi : (i : ℕ) + 1 ∈ Icc 1 (P.k - 1) := Finset.mem_Icc.2 ⟨by omega, by have := i.2; omega⟩
    have h1 := h _ hi
    rw [rho_eq P π _ (Finset.mem_Icc.1 hi), rho_eq P π' _ (Finset.mem_Icc.1 hi)] at h1
    have h2 : (((π ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) : ℝ) = (((π' ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) : ℝ) := by
      linarith
    have h3 : ((π ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) = ((π' ⟨(i : ℕ) + 1 - 1, by have := i.2; omega⟩ : Fin _) : ℕ) := by
      exact_mod_cast h2
    rw [val_congr P π _ i (Fin.ext (by simp)), val_congr P π' _ i (Fin.ext (by simp))] at h3
    exact h3

theorem ord (k : ℕ) (u u' ρ : ℕ → ℝ) (hI : I.Interlaces k u u' ρ) (l : ℕ) (hl : l ∈ Icc 1 (k - 1)) :
    (∀ i ∈ Icc 1 k, i ≤ l → u l ≤ u i ∧ u' l ≤ u' i) ∧ (∀ i ∈ Icc 1 k, l < i → u i ≤ u (l + 1) ∧ u' i ≤ u' (l + 1)) ∧
    (∀ j ∈ Icc 1 (k - 1), j < l → u l + 1 / 2 ≤ ρ j ∧ u' l + 1 / 2 ≤ ρ j) ∧
    (∀ j ∈ Icc 1 (k - 1), l < j → ρ j + 1 / 2 ≤ u (l + 1) ∧ ρ j + 1 / 2 ≤ u' (l + 1)) := by
  have hm := mono k u u' ρ hI
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (l - i) i hi'.1 (by omega)
    have e : i + (l - i) = l := by omega
    rwa [e] at c
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (i - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (i - (l + 1)) = i := by omega
    rwa [e] at c
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (l - (j + 1)) (j + 1) (by omega) (by omega)
    have e : j + 1 + (l - (j + 1)) = l := by omega
    rw [e] at c
    constructor <;> linarith [b.2.2.1, b.2.2.2, c.1, c.2]
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (j - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (j - (l + 1)) = j := by omega
    rw [e] at c
    constructor <;> linarith [b.1, b.2.1, c.1, c.2]

theorem nrm_pos (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    0 < Nrm P l π := by
  have hI := tyInterlaces P hP π
  have hI' := tyInterlaces P hP π'
  have hr := rhoUp P l π π' hU l hl
  rw [if_pos rfl] at hr
  have b' := hI' l hl
  rw [hr] at b'
  have b := hI l hl
  obtain ⟨o1, o2, o3, o4⟩ := ord P.k P.u P.u' (rho P π) hI l hl
  unfold Nrm I.qpoly
  apply div_pos
  · rw [neg_mul, neg_neg]
    apply mul_pos (mul_pos hP.T_pos hP.T'_pos)
    apply Finset.prod_pos
    intro i hi
    by_cases h : i ≤ l
    · have := o1 i hi h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o2 i hi (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hj1 := Finset.mem_of_mem_erase hj
    have hj2 := Finset.ne_of_mem_erase hj
    by_cases h : j < l
    · have := o3 j hj1 h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o4 j hj1 (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]

theorem nrm_down (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    NrmDown P l π' = Nrm P l π := by
  have hr := rhoUp P l π π' hU
  have hrl := hr l hl
  rw [if_pos rfl] at hrl
  unfold NrmDown Nrm
  rw [hrl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1) + 1) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  rw [e1, e2]
  congr 3
  ring

theorem top (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    rho P π l = P.hi l := by
  have hl' := Finset.mem_Icc.1 hl
  have e : l - 1 + 1 = l := by omega
  by_contra hne
  apply h
  have hlt : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) < P.wid l := by
    by_contra hge
    apply hne
    have h2 := (π ⟨l - 1, by omega⟩).2
    simp only [e] at h2
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = P.wid l := by omega
    rw [rho_eq P π l hl', h3, wid_eq P hP l hl]; ring
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) + 1, ?_⟩ else π i, ?_⟩
  · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [val_congr P π _ _ this, hi]; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · simp [hi]
    · simp [hi]

theorem bot (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π' π) :
    rho P π l = P.lo l := by
  have hl' := Finset.mem_Icc.1 hl
  by_contra hne
  apply h
  have hpos : 0 < ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) := by
    by_contra hge
    apply hne
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = 0 := by omega
    rw [rho_eq P π l hl', h3]; simp
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) - 1, ?_⟩ else π i, ?_⟩
  · have := (π i).2; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
      have h5 := val_congr P π _ _ this
      simp [hi]; omega
    · simp [hi]

theorem nrmFacts : NrmFacts := by
  intro P hP l hl π
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨fun π' hU => ⟨nrm_pos P hP l hl π π' hU, nrm_down P l hl π π' hU⟩, ?_, ?_⟩
  · intro h
    have ht := top P hP l hl π h
    unfold Nrm I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l - 1 + 1 / 2 + P.u i) * (-rho P π l - 1 + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
      rw [ht]; unfold Par.hi
      rcases min_choice (P.u l) (P.u' l) with h | h <;> rw [h] <;> ring
    rw [this]; simp
  · intro h
    have ht := bot P l hl π h
    unfold NrmDown I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [ht]; unfold Par.lo
      rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
    rw [this]; simp

theorem num_zero (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) = 0 := by
  have hl' := Finset.mem_Icc.1 hl
  have ht := top P hP l hl π h
  unfold I.qpoly
  have : ∏ i ∈ Icc 1 P.k, ((-rho P π l - 1 + 1 / 2 + P.u i) * (-rho P π l - 1 + 1 / 2 + P.u' i)) = 0 := by
    apply Finset.prod_eq_zero (i := l) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
    rw [ht]; unfold Par.hi
    rcases min_choice (P.u l) (P.u' l) with h | h <;> rw [h] <;> ring
  rw [this]; simp

theorem nrm_key (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    Nrm P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) := by
  by_cases h : ∃ π', Up P l π π'
  · obtain ⟨π', hU⟩ := h
    have hp := nrm_pos P hP l hl π π' hU
    have hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1)) ≠ 0 := by
      intro h0
      unfold Nrm at hp
      rw [h0, div_zero] at hp
      exact lt_irrefl _ hp
    unfold Nrm
    exact div_mul_cancel₀ _ hD
  · rw [(nrmFacts P hP l hl π).2.1 h, num_zero P hP l hl π h]; simp

theorem rho_inj (P : Par) (hP : P.OK) (π : Ty P) (i j : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hij : i < j) : rho P π j < rho P π i := by
  have hI := tyInterlaces P hP π
  have o := (ord P.k P.u P.u' (rho P π) hI i hi).2.2.2 j hj hij
  have b := hI i hi
  linarith [o.1, b.2.2.1]

open Polynomial in
theorem wExact : WExact := by
  intro P hP π
  have hmonic : (coordinatePolynomial P π).Monic := by
    unfold coordinatePolynomial
    exact monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hdvd : coordinatePolynomial P π ∣ wNum P π := by
    unfold coordinatePolynomial
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      show IsCoprime (X + C ((rho P π i : ℂ) + 1)) (X + C ((rho P π j : ℂ) + 1))
      have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
      rw [e, e]
      apply isCoprime_X_sub_C_of_isUnit_sub
      apply IsUnit.mk0
      intro h0
      have h1 : (rho P π i : ℂ) = rho P π j := by linear_combination -h0
      have h2 : rho P π i = rho P π j := by exact_mod_cast h1
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd h2 (ne_of_gt (rho_inj P hP π i j hi hj h))
      · exact absurd h2 (ne_of_lt (rho_inj P hP π j i hj hi h))
    · intro l hl
      have e : (X + C ((rho P π l : ℂ) + 1) : ℂ[X]) = X - C (-((rho P π l : ℂ) + 1)) := by rw [C_neg, sub_neg_eq_add]
      rw [e, dvd_iff_isRoot, IsRoot.def]
      unfold wNum
      rw [eval_add, eval_finsetSum, Finset.sum_eq_single l]
      · have hk := nrm_key P hP l hl π
        have hk' := congrArg (fun x : ℝ => (x : ℂ)) hk
        simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one] at hk'
        have hq : eval (-((rho P π l : ℂ) + 1)) (qP P) = ((I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) : ℝ) : ℂ) := by
          unfold qP I.qpoly
          simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
          push_cast
          congr 1
          refine Finset.prod_congr rfl ?_
          intro i _; ring
        rw [hq]
        simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
        have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) =
            ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1) :=
          Finset.prod_congr rfl (fun j _ => by ring)
        have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) =
            ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
          Finset.prod_congr rfl (fun j _ => by ring)
        rw [e1, e2, mul_comm (∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1)), hk']
        ring
      · intro m _ hml
        simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
        have : ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) = 0 :=
          Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)
        rw [this]; simp
      · intro h; exact absurd hl h
  have hmod := (modByMonic_eq_zero_iff_dvd hmonic).2 hdvd
  have := modByMonic_add_div (wNum P π) (coordinatePolynomial P π)
  rw [hmod, zero_add] at this
  exact this.symm

theorem realPoints : RealPoints := by
  intro P π Y
  constructor
  · simp [xC, I.xpoly]
  · simp [qC, I.qpoly]

theorem interlaceSignTwo : InterlaceSignTwo := by
  intro k u u' ρ l Y h1 h2 hI hC e he
  have he2 : -2 ≤ e ∧ e ≤ 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> norm_num
  have hm := mono k u u' ρ hI

  have hlow : ∀ i ∈ Icc 1 (l - 1), 0 < Y + e + ρ i := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have b := hI i (Finset.mem_Icc.2 ⟨hi'.1, by omega⟩)
    have c := hm (l - (i + 1)) (i + 1) (by omega) (by omega)
    have e1 : i + 1 + (l - (i + 1)) = l := by omega
    rw [e1] at c
    rcases hC with hC | hC <;> linarith [b.2.2.1, b.2.2.2, c.1, c.2, hC.1, hC.2]
  have hhigh : ∀ i ∈ Icc l (k - 1), 0 < -(Y + e + ρ i) := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have b := hI i (Finset.mem_Icc.2 ⟨by omega, hi'.2⟩)
    have c := hm (i - l) l h1 (by omega)
    have e1 : l + (i - l) = i := by omega
    rw [e1] at c
    rcases hC with hC | hC <;> linarith [b.1, b.2.1, c.1, c.2, hC.1, hC.2]
  have hsplit : Icc 1 (k - 1) = Icc 1 (l - 1) ∪ Icc l (k - 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Icc 1 (l - 1)) (Icc l (k - 1)) := by
    rw [Finset.disjoint_left]; intro i a b
    have := Finset.mem_Icc.1 a; have := Finset.mem_Icc.1 b; omega
  have hcard : (Icc l (k - 1)).card = k - l := by simp; omega
  unfold I.xpoly
  rw [hsplit, Finset.prod_union hdisj]
  have hneg : ∏ i ∈ Icc l (k - 1), (Y + e + ρ i) = (-1) ^ (k - l) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i)) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _; ring
  rw [hneg]
  have p1 := Finset.prod_pos hlow
  have p2 := Finset.prod_pos hhigh
  have sq : ((-1 : ℝ) ^ (k - l)) * (-1) ^ (k - l) = 1 := by rw [← mul_pow]; simp
  calc (0:ℝ) < (∏ i ∈ Icc 1 (l - 1), (Y + e + ρ i)) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i)) := mul_pos p1 p2
    _ = ((-1 : ℝ) ^ (k - l) * (-1) ^ (k - l)) * ((∏ i ∈ Icc 1 (l - 1), (Y + e + ρ i)) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i))) := by rw [sq, one_mul]
    _ = _ := by ring

end Formalism.FourierDecayAlt.P.Mx3

namespace Formalism.FourierDecayAlt.P

theorem types_interlace : Formalism.FourierDecayAlt.M.TyInterlaces := Mx3.tyInterlaces
theorem types_complete : Formalism.FourierDecayAlt.M.TyComplete := Mx3.tyComplete
theorem rho_raise : Formalism.FourierDecayAlt.M.RhoUp := Mx3.rhoUp
theorem nrmFacts_statement : Formalism.FourierDecayAlt.M.NrmFacts := Mx3.nrmFacts
theorem realPoints_statement : Formalism.FourierDecayAlt.M.RealPoints := Mx3.realPoints
theorem weight_exact : Formalism.FourierDecayAlt.M.WExact := Mx3.wExact
theorem interlace_sign_two : Formalism.FourierDecayAlt.M.InterlaceSignTwo := Mx3.interlaceSignTwo

end Formalism.FourierDecayAlt.P
