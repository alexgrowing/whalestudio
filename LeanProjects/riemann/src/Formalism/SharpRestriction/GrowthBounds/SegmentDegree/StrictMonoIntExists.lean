import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Supp

variable {σ τ R : Type*} [CommRing R]

theorem supp_one {m : σ →₀ ℕ} (hm : m ∈ (1 : MvPolynomial σ R).support) : m = 0 := by
  classical
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (by rw [MvPolynomial.coeff_one, if_neg (fun h' => h h'.symm)])

theorem supp_prod_bound {ι : Type*} (w : (σ →₀ ℕ) →+ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℝ)
    (h : ∀ j ∈ s, ∀ m ∈ (f j).support, (w m : ℝ) ≤ b j) :
    ∀ m ∈ (∏ j ∈ s, f j).support, (w m : ℝ) ≤ ∑ j ∈ s, b j := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ m hm
    rw [Finset.prod_empty] at hm
    rw [supp_one hm]
    simp
  · intro a s ha ih h m hm
    rw [Finset.prod_insert ha] at hm
    have hm' := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_mul] at hm'
    obtain ⟨⟨m1, m2⟩, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm'
    have hmem' : m1 + m2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
    have h1 : m1 ∈ (f a).support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have h2 : m2 ∈ (∏ j ∈ s, f j).support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    rw [Finset.sum_insert ha, ← hmem', map_add, Nat.cast_add]
    exact add_le_add (h a (Finset.mem_insert_self a s) m1 h1)
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) m2 h2)

def imgMon (g : σ → τ) (e : σ → ℕ) (m : σ →₀ ℕ) : τ →₀ ℕ := m.sum fun v n => Finsupp.single (g v) (e v * n)

theorem aeval_pow_monomial (g : σ → τ) (e : σ → ℕ) (m : σ →₀ ℕ) (c : R) :
    aeval (fun v => (X (g v) : MvPolynomial τ R) ^ e v) (monomial m c) = monomial (imgMon g e m) c := by
  rw [MvPolynomial.aeval_monomial, imgMon, MvPolynomial.monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro v _
  show (X (g v) ^ e v) ^ m v = _
  rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]

theorem supp_aeval_pow (g : σ → τ) (e : σ → ℕ) (x : MvPolynomial σ R) {m' : τ →₀ ℕ}
    (hm' : m' ∈ (aeval (fun v => (X (g v) : MvPolynomial τ R) ^ e v) x).support) :
    ∃ m ∈ x.support, m' = imgMon g e m := by
  classical
  by_contra hne
  push_neg at hne
  apply MvPolynomial.mem_support_iff.mp hm'
  rw [x.as_sum, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [aeval_pow_monomial, MvPolynomial.coeff_monomial, if_neg (fun h => hne m hm h.symm)]

end Supp

theorem posOf_val (n' : ℕ) [NeZero n'] (x : ℤ) : ((posOf n' x).val : ℤ) = x % (n' : ℤ) := by
  have h0 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne n'))
  have h1 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos n')
  show (((x % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _
  generalize x % (n' : ℤ) = y at *
  have h2 := Int.toNat_of_nonneg h0
  have h3 : y.toNat < n' := by omega
  rw [Nat.mod_eq_of_lt h3, h2]

theorem posOf_even {n' : ℕ} [NeZero n'] (he : Even n') (x : ℤ) : Even (posOf n' x).val ↔ Even x := by
  have hv := posOf_val n' x
  obtain ⟨k, hk⟩ := he
  have hn : (n' : ℤ) = k + k := by exact_mod_cast hk
  rw [hn] at hv
  have h2 : x % ((k : ℤ) + k) % 2 = x % 2 := Int.emod_emod_of_dvd x ⟨(k : ℤ), by ring⟩
  rw [Nat.even_iff, Int.even_iff]
  generalize x % ((k : ℤ) + k) = y at *
  generalize (posOf n' x).val = v at *
  omega

theorem posOf_natCast {n' : ℕ} [NeZero n'] (t : Fin n') : posOf n' (t.val : ℤ) = t := by
  apply Fin.ext
  have h := posOf_val n' (t.val : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast t.isLt)] at h
  exact_mod_cast h

theorem posOf_injOn {n' : ℕ} [NeZero n'] (a : ℤ) :
    Set.InjOn (posOf n') (Set.Ioc a (a + n')) := by
  intro x hx y hy hxy
  have h1 := posOf_val n' x
  have h2 := posOf_val n' y
  rw [hxy] at h1
  rw [Set.mem_Ioc] at hx hy
  have hmod : Int.ModEq n' y x := (h1.symm.trans h2).symm
  obtain ⟨c, hc⟩ := Int.ModEq.dvd hmod
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hc1 : c < 1 := by
    by_contra h
    push_neg at h
    have : (n' : ℤ) * 1 ≤ n' * c := mul_le_mul_of_nonneg_left h hn.le
    omega
  have hc2 : -1 < c := by
    by_contra h
    push_neg at h
    have : (n' : ℤ) * c ≤ n' * (-1) := mul_le_mul_of_nonneg_left h hn.le
    omega
  have : c = 0 := by omega
  subst this
  omega

section Wt

variable {n' r K : ℕ}

def wtVS (v : Fin n' × Fin (r + K)) : ℕ :=
  if Even v.1.val then (if r ≤ v.2.val then 1 else 0) else (if v.2.val < r then 1 else 0)

theorem sum_wtVS (f : Fin (r + K) → ℕ) (t : Fin n') :
    ∑ c : Fin (r + K), f c * wtVS (t, c) =
      if Even t.val then ∑ c : Fin K, f (Fin.natAdd r c) else ∑ c : Fin r, f (Fin.castAdd K c) := by
  have hi : ∀ i : Fin r, ¬ r ≤ (i : ℕ) := fun i => not_le.mpr i.isLt
  rw [Fin.sum_univ_add]
  split_ifs with h
  · simp [wtVS, h, hi]
  · simp [wtVS, h, hi]

theorem vsDeg_eq (m : Fin n' × Fin (r + K) →₀ ℕ) : vsDeg m = Finsupp.linearCombination ℕ wtVS m := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  unfold vsDeg
  refine Finset.sum_congr rfl fun t _ => ?_
  have := sum_wtVS (fun c => m (t, c)) t
  beta_reduce at this
  simp only [smul_eq_mul]
  rw [this]

end Wt

section Fr

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r)

def eFr (j : ℤ) : ℤ := F.fr j (r - 1)

variable {F} {L₁ N₁ : ℕ}

theorem fr_zero_le (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j k (by omega)))

theorem fr_zero_le_eFr [NeZero r] (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr j 0 ≤ eFr F j := by
  exact fr_zero_le hV j (r - 1) (by have := NeZero.pos r; omega)

theorem eFr_strictMono [NeZero r] (hV : F.Valid L₁ N₁) : StrictMono (eFr F) := by
  exact strictMono_int_of_lt_succ fun j => lt_of_lt_of_le (hV.2.2.2.1 j) (fr_zero_le_eFr hV (j + 1))

theorem strictMono_int_exists (e : ℤ → ℤ) (he : StrictMono e) (x : ℤ) : ∃ j, e (j - 1) < x ∧ x ≤ e j := by
  classical
  have hup : ∀ n : ℕ, e 0 + n ≤ e n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := he (show (k : ℤ) < ((k + 1 : ℕ) : ℤ) by push_cast; omega)
      push_cast at this ⊢
      omega
  have hdn : ∀ n : ℕ, e (-(n : ℤ)) ≤ e 0 - n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := he (show (-((k + 1 : ℕ) : ℤ)) < -(k : ℤ) by push_cast; omega)
      push_cast at this ⊢
      omega
  have hbdd : ∃ b : ℤ, ∀ z, x ≤ e z → b ≤ z := by
    refine ⟨min 0 (x - e 0), fun z hz => ?_⟩
    by_cases h : 0 ≤ z
    · exact le_trans (min_le_left _ _) h
    · have h3 : (((-z).toNat : ℕ) : ℤ) = -z := Int.toNat_of_nonneg (by omega)
      have h4 := hdn (-z).toNat
      rw [h3, neg_neg] at h4
      have h5 : x - e 0 ≤ z := by omega
      exact le_trans (min_le_right _ _) h5
  have hinh : ∃ z, x ≤ e z := by
    refine ⟨((max 0 (x - e 0)).toNat : ℤ), ?_⟩
    have h1 := hup (max 0 (x - e 0)).toNat
    have h2 : (((max 0 (x - e 0)).toNat : ℕ) : ℤ) = max 0 (x - e 0) := Int.toNat_of_nonneg (le_max_left _ _)
    rw [h2] at h1 ⊢
    have := le_max_right 0 (x - e 0)
    linarith
  obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨j, ?_, hj⟩
  by_contra h
  push_neg at h
  have := hmin (j - 1) h
  omega

open Classical in

def nonW (F : Frames n' r) (j : ℤ) : Finset ℤ := (F.letters j).filter fun x => ¬ F.IsW j x

open Classical in
theorem nonW_eq [NeZero r] (hV : F.Valid L₁ N₁) (j : ℤ) :
    nonW F j = (Finset.Ioc (eFr F (j - 1)) (eFr F j)).filter fun x => posOf n' x ∈ F.TT := by
  ext x
  have h0 := fr_zero_le_eFr hV (j - 1)
  unfold eFr at h0 ⊢
  unfold nonW Frames.letters Frames.IsW
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩

theorem exists_nonW [NeZero r] (hV : F.Valid L₁ N₁) (t : Fin n') (ht : t ∈ F.TT) :
    ∃ j : ℤ, ∃ x ∈ F.letters j, ¬ F.IsW j x ∧ posOf n' x = t := by
  classical
  obtain ⟨j, hj1, hj2⟩ := strictMono_int_exists (eFr F) (eFr_strictMono hV) (t.val : ℤ)
  have hx : (t.val : ℤ) ∈ nonW F j := by
    rw [nonW_eq hV j, Finset.mem_filter, Finset.mem_Ioc, posOf_natCast]
    exact ⟨⟨hj1, hj2⟩, ht⟩
  unfold nonW at hx
  rw [Finset.mem_filter] at hx
  exact ⟨j, (t.val : ℤ), hx.1, hx.2, posOf_natCast t⟩

theorem sum_card_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (m : ℕ) :
    ∑ j ∈ Finset.range m, ((Finset.Ioc (g j) (g (j + 1))).filter P).card = ((Finset.Ioc (g 0) (g m)).filter P).card := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : g 0 ≤ g k := hg (Nat.zero_le k)
    have h2 : g k ≤ g (k + 1) := hg (Nat.le_succ k)
    rw [← Finset.Ioc_union_Ioc_eq_Ioc h1 h2, Finset.filter_union, Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx1 hx2
      omega

theorem sum_card_nonW [NeZero r] (hV : F.Valid L₁ N₁) :
    ∑ j ∈ Finset.range F.J, (nonW F (j : ℤ)).card ≤ F.TT.card := by
  classical
  have hmono : Monotone (fun i : ℕ => eFr F ((i : ℤ) - 1)) := fun a b hab =>
    (eFr_strictMono hV).monotone (by have : (a : ℤ) ≤ b := by exact_mod_cast hab
                                     omega)
  have h1 : ∀ j ∈ Finset.range F.J, (nonW F (j : ℤ)).card =
      ((Finset.Ioc ((fun i : ℕ => eFr F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ F.TT)).card := by
    intro j _
    rw [nonW_eq hV]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [Finset.sum_congr rfl h1, sum_card_Ioc _ hmono]
  simp only [Nat.cast_zero, zero_sub]
  have hlen : eFr F ((F.J : ℤ) - 1) = eFr F (-1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    unfold eFr
    rw [← this, show (F.J : ℤ) - 1 = -1 + F.J by ring]
  refine Finset.card_le_card_of_injOn (posOf n') ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    simpa [Finset.mem_coe] using hx.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hx hy
    refine posOf_injOn (eFr F (-1)) ?_ ?_ hxy
    · rw [Set.mem_Ioc]; constructor <;> omega
    · rw [Set.mem_Ioc]; constructor <;> omega

end Fr

section Seg

variable {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K]

def okVars (F : Frames n' r) (K : ℕ) (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | v.1 ∈ F.letters j ∧ (r ≤ v.2.val → ¬ F.IsW j v.1)}

theorem XX'_supported (O : Type) [CommRing O] (F : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ)
    {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) : x ∈ supported O (okVars F K j) := by
  classical
  unfold XX' at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (supported O (okVars F K j)))).mpr ?_ hx1
  rintro P ⟨A, G, M, hA, hG, -, rfl⟩
  rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
  refine Subalgebra.mul_mem _ ?_ ?_
  · rw [MvPolynomial.mem_supported] at hA ⊢
    unfold plEmb
    refine (Finset.coe_subset.mpr (MvPolynomial.vars_rename (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) A)).trans ?_
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 : w.1 ∈ F.letters j := hA (Finset.mem_coe.mpr hw)
    simp only [okVars, Set.mem_setOf_eq]
    refine ⟨h1, fun h => ?_⟩
    exfalso
    have := w.2.isLt
    simp only [Fin.coe_castAdd] at h
    omega
  · rw [MvPolynomial.mem_supported] at hG ⊢
    unfold nmEmb
    refine (Finset.coe_subset.mpr (MvPolynomial.vars_rename (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) G)).trans ?_
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 : w.1 ∈ F.letters j ∧ ¬ F.IsW j w.1 := hG (Finset.mem_coe.mpr hw)
    simp only [okVars, Set.mem_setOf_eq]
    exact ⟨h1.1, fun _ => h1.2⟩

theorem ordDeg_eq (he : Even n') (m : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) :
    ordDeg m x = ∑ c : Fin (r + K), m (x, c) * wtVS (posOf n' x, c) := by
  have := sum_wtVS (fun c => m (x, c)) (posOf n' x)
  beta_reduce at this
  rw [this]
  unfold ordDeg
  simp only [posOf_even he]

private theorem even_of_isW {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) {j x : ℤ}
    (hx : x ∈ F.letters j) (hw : F.IsW j x) : Even x := by
  unfold Frames.letters at hx
  unfold Frames.IsW at hw
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx0, -⟩, hT⟩ := hx
  have key : ∀ i, i < r → x ≤ F.fr (j - 1) i → ∃ i', i' < r ∧ x = F.fr (j - 1) i' := by
    intro i
    induction i with
    | zero => intro hi h; exact ⟨0, hi, le_antisymm h hx0⟩
    | succ k ih =>
      intro hi h
      by_cases hk : x ≤ F.fr (j - 1) k
      · exact ih (by omega) hk
      · by_cases he : x = F.fr (j - 1) (k + 1)
        · exact ⟨k + 1, hi, he⟩
        · exact absurd hT (hV.2.2.2.2.2.1 (j - 1) k x hi (by omega) (by omega))
  obtain ⟨i', hi', rfl⟩ := key (r - 1) (by have := NeZero.pos r; omega) hw
  exact (hV.2.2.2.2.1 (j - 1) i' hi').2

theorem vs_img_le (he : Even n') {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (p : ℕ) (j : ℤ)
    (m : ℤ × Fin (r + K) →₀ ℕ) (hm : ∀ v ∈ m.support, v ∈ okVars F K j) :
    vsDeg (imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ F.dist j v.1) m) ≤
      ∑ x ∈ nonW F j, p ^ F.dist j x * ordDeg m x := by
  classical
  rw [vsDeg_eq, imgMon, Finsupp.sum, map_sum]
  simp only [Finsupp.linearCombination_single, smul_eq_mul]
  calc ∑ v ∈ m.support, p ^ F.dist j v.1 * m v * wtVS (posOf n' v.1, v.2)
      ≤ ∑ v ∈ nonW F j ×ˢ (Finset.univ : Finset (Fin (r + K))), p ^ F.dist j v.1 * m v * wtVS (posOf n' v.1, v.2) := by
        apply Finset.sum_le_sum_of_ne_zero
        intro v hv hne
        have hok := hm v hv
        simp only [okVars, Set.mem_setOf_eq] at hok
        rw [Finset.mem_product]
        refine ⟨?_, Finset.mem_univ _⟩
        simp only [nonW, Finset.mem_filter]
        refine ⟨hok.1, fun hw => hne ?_⟩
        have hev : Even v.1 := even_of_isW hV hok.1 hw
        have hlt : ¬ r ≤ (v.2 : ℕ) := fun h => hok.2 h hw
        have hpe : Even (posOf n' v.1).val := (posOf_even he v.1).mpr hev
        simp [wtVS, hpe, hlt]
    _ = ∑ x ∈ nonW F j, p ^ F.dist j x * ordDeg m x := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ordDeg_eq he, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring

end Seg

section Num

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def B1 : ℝ := X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + 10 * X.a * (p : ℝ) ^ (-(X.L₁ : ℤ))

omit [NeZero n'] in
theorem k_pos (hr : 0 < r) : (0 : ℝ) < Dat.k (r := r) K := by
  unfold Dat.k
  exact_mod_cast (show 0 < r + K by omega)

theorem pow_mul_o_le (hp : 0 < p) (hr : 0 < r) (ha : 0 ≤ X.a) (j x : ℤ) :
    (p : ℝ) ^ X.F.dist j x * X.o p K j x ≤ B1 X p K := by
  unfold Dat.o B1
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hpd : (0:ℝ) < (p:ℝ) ^ X.F.dist j x := pow_pos hp' _
  have hk := (k_pos K hr).ne'
  have hz : (p:ℝ) ^ X.F.dist j x * (p:ℝ) ^ (-((X.L₁:ℤ) + (X.F.dist j x : ℤ))) = (p:ℝ) ^ (-(X.L₁:ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hp'.ne']
    congr 1
    ring
  have h1 : (p:ℝ) ^ X.F.dist j x * (X.La * X.a / (↑p * Dat.k (r := r) K * ↑p ^ X.F.dist j x)) = X.La * X.a / (↑p * Dat.k (r := r) K) := by
    field_simp
  have hc : (if Even x then (10:ℝ) else 1) ≤ 10 := by split_ifs <;> norm_num
  have hpL : (0:ℝ) ≤ (p:ℝ) ^ (-(X.L₁:ℤ)) := by positivity
  rw [mul_add, h1]
  have h2 : (p:ℝ) ^ X.F.dist j x * ((if Even x then (10:ℝ) else 1) * X.a * (p:ℝ) ^ (-((X.L₁:ℤ) + (X.F.dist j x : ℤ)))) = (if Even x then (10:ℝ) else 1) * X.a * (p:ℝ) ^ (-(X.L₁:ℤ)) := by
    rw [← hz]
    ring
  rw [h2]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ha) hpL
  linarith

variable {X p K}

theorem eFr_mem_letters [NeZero r] (hX : X.Hyp p K) (j : ℤ) : eFr X.F j ∈ X.F.letters j := by
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have h1 := fr_zero_le_eFr hV (j - 1)
  have h2 := eFr_strictMono hV (show j - 1 < j by omega)
  have h3 := (hV.2.2.2.2.1 j (r - 1) (by omega)).1
  unfold eFr at h1 h2 ⊢
  unfold Frames.letters
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, le_refl _⟩, h3⟩

theorem Q_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.Q := by
  have h := hX.twist 0 (eFr X.F 0) (eFr_mem_letters hX 0)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast hX.prime.one_lt.le
  exact le_trans (one_le_pow₀ hp) h

theorem Ns_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.Ns := by
  have h1 := Finset.card_pos.mpr ⟨_, eFr_mem_letters hX 0⟩
  have h2 := hX.card 0
  omega

theorem a_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.a := by
  refine le_trans ?_ hX.P3
  refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) ?_) ?_) ?_) ?_) ?_) ?_
  · exact_mod_cast hX.prime.one_lt.le
  · exact hX.Y1
  · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ r + K by have := NeZero.pos r; omega))
  · exact_mod_cast Ns_one_le hX
  · exact one_le_pow₀ (Q_one_le hX)
  · norm_cast
    omega

end Num

section Main

variable {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r} {p : ℕ}

theorem seg_bound (O : Type) [CommRing O] (hX : X.Hyp p K) (j : ℤ) {x : SegRing O r K} (hx : x ∈ X.XXs p K O j)
    {m' : Fin n' × Fin (r + K) →₀ ℕ} (hm' : m' ∈ (phSeg O K p X.F j x).support) :
    (vsDeg m' : ℝ) ≤ ((nonW X.F j).card : ℝ) * B1 X p K := by
  classical
  unfold Dat.XXs at hx
  have hV := hX.valid
  have hsupp := XX'_supported O X.F j (X.mg p K j) (X.th p j) (X.o p K j) hx
  unfold XX' at hx
  have hres0 := (Submodule.mem_inf.mp hx).2
  rw [MvPolynomial.mem_restrictSupport_iff] at hres0
  unfold phSeg at hm'
  obtain ⟨mm, hmm, rfl⟩ := supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ X.F.dist j v.1) x hm'
  have hres : ∀ y ∈ X.F.letters j, ¬ X.F.IsW j y → (ordDeg mm y : ℝ) ≤ X.o p K j y :=
    hres0 (Finset.mem_coe.mpr hmm)
  have hsupp' := MvPolynomial.mem_supported.mp hsupp
  have hm : ∀ v ∈ mm.support, v ∈ okVars X.F K j := fun v hv =>
    hsupp' (Finset.mem_coe.mpr ((MvPolynomial.mem_vars v).mpr ⟨mm, hmm, hv⟩))
  have hmain := vs_img_le hX.even hV p j mm hm
  have hmain' := (Nat.cast_le (α := ℝ)).mpr hmain
  have hp : 0 < p := hX.prime.pos
  have hr : 0 < r := NeZero.pos r
  have ha : 0 ≤ X.a := le_trans zero_le_one (a_one_le hX)
  have hsum : ((∑ y ∈ nonW X.F j, p ^ X.F.dist j y * ordDeg mm y : ℕ) : ℝ) ≤ ∑ y ∈ nonW X.F j, B1 X p K := by
    push_cast
    refine Finset.sum_le_sum fun y hy => ?_
    have hy' : y ∈ X.F.letters j ∧ ¬ X.F.IsW j y := by simpa [nonW] using hy
    have h1 : (ordDeg mm y : ℝ) ≤ X.o p K j y := hres y hy'.1 hy'.2
    have h2 := pow_mul_o_le X p K hp hr ha j y
    have h3 : (0:ℝ) ≤ (p:ℝ) ^ X.F.dist j y := by positivity
    calc (p:ℝ) ^ X.F.dist j y * (ordDeg mm y : ℝ) ≤ (p:ℝ) ^ X.F.dist j y * X.o p K j y :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ B1 X p K := h2
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  exact le_trans hmain' hsum

theorem vsDeg_sum (m : Fin n' × Fin (r + K) →₀ ℕ) :
    vsDeg m = ∑ t : Fin n', ∑ c : Fin (r + K), m (t, c) * wtVS (t, c) := by
  unfold vsDeg
  refine Finset.sum_congr rfl fun t _ => ?_
  have := sum_wtVS (fun c => m (t, c)) t
  beta_reduce at this
  exact this.symm

theorem label_bound (hX : X.Hyp p K) (l : Fin n' × Fin (r + K) →₀ ℕ) (hl : IsLabel p X.F l)
    (h0 : ∀ t, t ∉ X.F.TT → ∀ c, l (t, c) = 0) :
    (vsDeg l : ℝ) ≤ (X.F.TT.card : ℝ) * (Dat.k (r := r) K * X.Q) := by
  have hV := hX.valid
  have hc : ∀ t ∈ X.F.TT, ∀ c, (l (t, c) : ℝ) ≤ X.Q := by
    intro t ht c
    obtain ⟨j, x, hx, hw, rfl⟩ := exists_nonW hV t ht
    have h1 := hl j x hx hw c
    have h2 := hX.twist j x hx
    have h3 : ((l (posOf n' x, c) : ℕ) : ℝ) < (p : ℝ) ^ X.F.dist j x := by exact_mod_cast h1
    linarith
  have hterm : ∀ t : Fin n', (∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ)) ≤
      if t ∈ X.F.TT then Dat.k (r := r) K * X.Q else 0 := by
    intro t
    split_ifs with ht
    · calc (∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ)) ≤ ∑ c : Fin (r + K), X.Q := by
            refine Finset.sum_le_sum fun c _ => ?_
            have hw : (wtVS (t, c) : ℝ) ≤ 1 := by
              unfold wtVS
              split_ifs <;> norm_num
            have hw0 : (0:ℝ) ≤ (wtVS (t, c) : ℝ) := Nat.cast_nonneg _
            have hl0 : (0:ℝ) ≤ (l (t, c) : ℝ) := Nat.cast_nonneg _
            nlinarith [hc t ht c]
        _ = Dat.k (r := r) K * X.Q := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rfl
    · have : ∀ c, l (t, c) = 0 := h0 t ht
      simp [this]
  rw [vsDeg_sum]
  push_cast
  calc (∑ t : Fin n', ∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ))
      ≤ ∑ t : Fin n', (if t ∈ X.F.TT then Dat.k (r := r) K * X.Q else 0) := Finset.sum_le_sum fun t _ => hterm t
    _ = (X.F.TT.card : ℝ) * (Dat.k (r := r) K * X.Q) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

theorem gen_bound (O : Type) [CommRing O] (hX : X.Hyp p K) (hC : 0 ≤ X.CLa) {P : RRing O n' (r + K)}
    (hP : P ∈ X.gen p K O) {mm : Fin n' × Fin (r + K) →₀ ℕ} (hmm : mm ∈ P.support) :
    (vsDeg mm : ℝ) ≤ 10 * (X.F.TT.card : ℝ) *
        (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + X.a * (p : ℝ) ^ (-(X.L₁ : ℤ)) + Dat.k (r := r) K * X.Q) := by
  classical
  obtain ⟨x, hx, l, hl, rfl, hdeg⟩ := hP
  by_cases hle : l ≤ mm
  swap
  · exfalso
    apply MvPolynomial.mem_support_iff.mp hmm
    rw [MvPolynomial.coeff_mul_monomial', if_neg hle]
  have hm'' : mm - l ∈ (∏ j ∈ Finset.range X.F.J, (phSeg O K p X.F (j : ℤ)) (x j)).support := by
    have hcoef := MvPolynomial.mem_support_iff.mp hmm
    rw [MvPolynomial.coeff_mul_monomial', if_pos hle, mul_one] at hcoef
    exact MvPolynomial.mem_support_iff.mpr hcoef
  have hadd : vsDeg mm = vsDeg (mm - l) + vsDeg l := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [vsDeg_eq, vsDeg_eq, vsDeg_eq, map_add]
  unfold RRdeg Dat.d at hdeg
  rw [MvPolynomial.mem_restrictSupport_iff] at hdeg
  have hrow := hdeg (Finset.mem_coe.mpr hmm)
  simp only [Set.mem_setOf_eq] at hrow
  have h0 : ∀ t, t ∉ X.F.TT → ∀ c, l (t, c) = 0 := by
    intro t ht c
    have h1 : ∑ c, mm (t, c) = 0 := by
      have := hrow t
      simpa [ht] using this
    have h2 : mm (t, c) = 0 := (Finset.sum_eq_zero_iff.mp h1) c (Finset.mem_univ _)
    have h3 : l (t, c) ≤ mm (t, c) := (Finsupp.le_def.mp hle) (t, c)
    omega
  have hL := label_bound hX l hl h0
  have hT : (0:ℝ) ≤ X.F.TT.card := Nat.cast_nonneg _
  have ha := a_one_le hX
  have hp' : (0:ℝ) < p := by exact_mod_cast hX.prime.pos
  have hk := k_pos K (NeZero.pos r)
  have hLa : 0 ≤ X.La := by
    unfold Dat.La
    have : 0 ≤ Real.log X.a := Real.log_nonneg ha
    exact mul_nonneg (mul_nonneg hC (by positivity)) this
  have hA : 0 ≤ X.La * X.a / (↑p * Dat.k (r := r) K) :=
    div_nonneg (mul_nonneg hLa (by linarith)) (mul_pos hp' hk).le
  have hPq : 0 ≤ X.a * (p:ℝ) ^ (-(X.L₁ : ℤ)) := mul_nonneg (by linarith) (by positivity)
  have hC' : 0 ≤ Dat.k (r := r) K * X.Q := mul_nonneg hk.le (le_trans zero_le_one (Q_one_le hX))
  have hB1 : 0 ≤ B1 X p K := by
    unfold B1
    exact add_nonneg hA (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity))
  have hprod := supp_prod_bound (Finsupp.linearCombination ℕ (wtVS (n' := n') (r := r) (K := K))).toAddMonoidHom
    (Finset.range X.F.J) (fun j : ℕ => (phSeg O K p X.F (j : ℤ)) (x j))
    (fun j : ℕ => ((nonW X.F (j : ℤ)).card : ℝ) * B1 X p K) (fun j _ m hm => by
      have := seg_bound O hX (j : ℤ) (hx j) hm
      rw [vsDeg_eq] at this
      exact this) (mm - l) hm''
  have hsumc := sum_card_nonW hX.valid
  have hsumc' : (∑ j ∈ Finset.range X.F.J, ((nonW X.F (j : ℤ)).card : ℝ)) ≤ X.F.TT.card := by
    exact_mod_cast hsumc
  have hQ' : (vsDeg (mm - l) : ℝ) ≤ X.F.TT.card * B1 X p K := by
    rw [vsDeg_eq]
    refine le_trans hprod ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsumc' hB1
  have hB1' : B1 X p K = X.La * X.a / (↑p * Dat.k (r := r) K) + 10 * X.a * (p:ℝ) ^ (-(X.L₁ : ℤ)) := rfl
  rw [hB1'] at hQ'
  rw [hadd, Nat.cast_add]
  nlinarith [mul_nonneg hT hA, mul_nonneg hT hC', mul_nonneg hT hPq, hQ', hL]

theorem restDeg : RestDeg := by
  unfold RestDeg
  intro p n' r K _ _ _ X O _ _ hX hC P hP mm hmm
  unfold Dat.NN at hP
  revert hmm
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact fun h => gen_bound O hX hC hQ h
  | zero => intro h; simp at h
  | add Q1 Q2 _ _ ih1 ih2 =>
    intro h
    classical
    rcases Finset.mem_union.mp (MvPolynomial.support_add h) with h' | h'
    · exact ih1 h'
    · exact ih2 h'
  | smul a Q _ ih => exact fun h => ih (MvPolynomial.support_smul h)

end Main

end Formalism.MainNotions.SelectionLemmas.Pf
