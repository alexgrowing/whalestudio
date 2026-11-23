import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUdlOfIsUnit

namespace GlobalTheory.CompanionTheory.KmCover

open Matrix

section Solve

variable {R : Type*} [CommRing R] {n : ℕ}

theorem mul_congr_one {J : Ideal R} {a b : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J)
    (hb : ∀ i j, b i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) :
    ∀ i j, (a * b) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J := by
  intro i j
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  have e2 : (a * b) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
      ((a - 1) * (b - 1)) i j + (a i j - (1 : Matrix (Fin n) (Fin n) R) i j) +
        (b i j - (1 : Matrix (Fin n) (Fin n) R) i j) := by
    rw [← Matrix.sub_apply, e]
    rfl
  rw [e2]
  refine J.add_mem (J.add_mem ?_ (ha i j)) (hb i j)
  rw [Matrix.mul_apply]
  exact J.sum_mem fun k _ => J.mul_mem_right _ (ha i k)

theorem solve_unitriangular (J : Ideal R) (T V : Fin n → Fin n → Set R)
    (hdec : ∀ i j, i < j → ∀ c ∈ J, ∃ t v : R, t ∈ T i j ∧ v ∈ V i j ∧ t ∈ J ∧ v ∈ J ∧ c = t + v)
    (u : Matrix (Fin n) (Fin n) R)
    (hu : ∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J)
    (hlow : ∀ i j, j < i → u i j = 0) (hdiag : ∀ i, u i i = 1) :
    ∃ r w : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → r i j = 0) ∧ (∀ i, r i i = 1) ∧ (∀ i j, i < j → r i j ∈ T i j) ∧
      (∀ i j, j < i → w i j = 0) ∧ (∀ i, w i i = 1) ∧ (∀ i j, i < j → w i j ∈ V i j) ∧
      u = r * w := by
  have key : ∀ d : ℕ, ∃ r w : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → r i j = 0) ∧ (∀ i, r i i = 1) ∧
      (∀ i j, j < i → w i j = 0) ∧ (∀ i, w i i = 1) ∧
      (∀ i j, i < j → j.val ≤ i.val + d → r i j ∈ T i j ∧ w i j ∈ V i j) ∧
      (∀ i j, i.val + d < j.val → r i j = 0 ∧ w i j = 0) ∧
      (∀ i j, r i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) ∧
      (∀ i j, w i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J) ∧
      (∀ i j, j.val ≤ i.val + d → (r * w) i j = u i j) := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j h
        exact Matrix.one_apply_ne (ne_of_gt h)
      · intro i
        exact Matrix.one_apply_eq i
      · intro i j h
        exact Matrix.one_apply_ne (ne_of_gt h)
      · intro i
        exact Matrix.one_apply_eq i
      · intro i j h h2
        have : i.val < j.val := h
        omega
      · intro i j h
        have : i ≠ j := by
          intro e
          subst e
          omega
        exact ⟨Matrix.one_apply_ne this, Matrix.one_apply_ne this⟩
      · intro i j
        simp
      · intro i j
        simp
      · intro i j h
        rw [mul_one]
        rcases Nat.lt_or_ge j.val i.val with h1 | h1
        · rw [hlow i j h1]
          exact Matrix.one_apply_ne (by
            intro e
            subst e
            omega)
        · have : i = j := Fin.ext (by omega)
          subst this
          rw [hdiag i]
          exact Matrix.one_apply_eq i
    | succ d ih =>
      obtain ⟨r, w, hrl, hrd, hwl, hwd, hin, hout, hrJ, hwJ, hp⟩ := ih
      have hc : ∀ i j, i < j → u i j - (r * w) i j ∈ J := by
        intro i j h
        have h1 := mul_congr_one hrJ hwJ i j
        have h2 := hu i j
        have := J.sub_mem h2 h1
        simpa using this
      have hex : ∀ i j, ∃ t v : R, i < j → t ∈ T i j ∧ v ∈ V i j ∧ t ∈ J ∧ v ∈ J ∧
          u i j - (r * w) i j = t + v := by
        intro i j
        by_cases h : i < j
        · obtain ⟨t, v, h1⟩ := hdec i j h _ (hc i j h)
          exact ⟨t, v, fun _ => h1⟩
        · exact ⟨0, 0, fun h' => absurd h' h⟩
      choose t v htv using hex
      obtain ⟨r', hr'⟩ : ∃ r' : Matrix (Fin n) (Fin n) R,
          ∀ i j, r' i j = if j.val = i.val + d + 1 then t i j else r i j :=
        ⟨fun i j => if j.val = i.val + d + 1 then t i j else r i j, fun _ _ => rfl⟩
      obtain ⟨w', hw'⟩ : ∃ w' : Matrix (Fin n) (Fin n) R,
          ∀ i j, w' i j = if j.val = i.val + d + 1 then v i j else w i j :=
        ⟨fun i j => if j.val = i.val + d + 1 then v i j else w i j, fun _ _ => rfl⟩
      have hr'l : ∀ i j, j < i → r' i j = 0 := by
        intro i j h
        have h' : j.val < i.val := h
        rw [hr', if_neg (by omega), hrl i j h]
      have hw'l : ∀ i j, j < i → w' i j = 0 := by
        intro i j h
        have h' : j.val < i.val := h
        rw [hw', if_neg (by omega), hwl i j h]
      have hr'd : ∀ i, r' i i = 1 := by
        intro i
        rw [hr', if_neg (by omega), hrd i]
      have hw'd : ∀ i, w' i i = 1 := by
        intro i
        rw [hw', if_neg (by omega), hwd i]
      refine ⟨r', w', hr'l, hr'd, hw'l, hw'd, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j h h2
        rw [hr', hw']
        by_cases e : j.val = i.val + d + 1
        · rw [if_pos e, if_pos e]
          exact ⟨(htv i j h).1, (htv i j h).2.1⟩
        · rw [if_neg e, if_neg e]
          exact hin i j h (by omega)
      · intro i j h
        rw [hr', hw', if_neg (by omega), if_neg (by omega)]
        exact hout i j (by omega)
      · intro i j
        rw [hr']
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          rw [if_pos e, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]
          exact (htv i j hij).2.2.1
        · rw [if_neg e]
          exact hrJ i j
      · intro i j
        rw [hw']
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          rw [if_pos e, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]
          exact (htv i j hij).2.2.2.1
        · rw [if_neg e]
          exact hwJ i j
      · intro i j h
        by_cases e : j.val = i.val + d + 1
        · have hij : i < j := by
            rw [Fin.lt_def]
            omega
          have hneq : i ≠ j := ne_of_lt hij
          have hold := hout i j (by omega)
          have hsum : (r' * w') i j = (r * w) i j + t i j + v i j := by
            have hterm : ∀ k, r' i k * w' k j =
                r i k * w k j + (if k = j then t i j else 0) + (if k = i then v i j else 0) := by
              intro k
              by_cases kj : k = j
              · subst kj
                rw [if_pos rfl, if_neg (Ne.symm hneq), hw'd, hwd, hold.1, hr', if_pos e]
                ring
              · by_cases ki : k = i
                · subst ki
                  rw [if_neg kj, if_pos rfl, hr'd, hrd, hold.2, hw', if_pos e]
                  ring
                · rw [if_neg kj, if_neg ki]
                  rcases lt_or_gt_of_ne ki with h1 | h1
                  · rw [hr'l i k h1, hrl i k h1]
                    ring
                  · rcases lt_or_gt_of_ne kj with h2 | h2
                    · have a1 : i.val < k.val := h1
                      have a2 : k.val < j.val := h2
                      rw [hr', hw', if_neg (by omega), if_neg (by omega)]
                      ring
                    · rw [hw'l k j h2, hwl k j h2]
                      ring
            rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hterm k),
              Finset.sum_add_distrib, Finset.sum_add_distrib, Matrix.mul_apply]
            simp
          rw [hsum]
          have := (htv i j hij).2.2.2.2
          linear_combination -this
        · have hle : j.val ≤ i.val + d := by omega
          rw [← hp i j hle, Matrix.mul_apply, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h1 : k.val = i.val + d + 1
          · have : j < k := by
              rw [Fin.lt_def]
              omega
            rw [hw'l k j this, hwl k j this]
            ring
          · by_cases h2 : j.val = k.val + d + 1
            · have : k < i := by
                rw [Fin.lt_def]
                omega
              rw [hr'l i k this, hrl i k this]
              ring
            · rw [hr', hw', if_neg h1, if_neg h2]
  obtain ⟨r, w, hrl, hrd, hwl, hwd, hin, -, -, -, hp⟩ := key n
  refine ⟨r, w, hrl, hrd, ?_, hwl, hwd, ?_, ?_⟩
  · intro i j h
    exact (hin i j h (by omega)).1
  · intro i j h
    exact (hin i j h (by omega)).2
  · ext i j
    exact (hp i j (by omega)).symm

end Solve

section Reps

theorem exists_reps (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    ∃ S : Finset R, S.card ≤ Nat.card (IsLocalRing.ResidueField R) ^ k ∧
      ∀ x : R, ∃ t ∈ S, x - t ∈ Ideal.span {ϖ ^ k} := by
  classical
  obtain ⟨S₁, hS₁, hS₁'⟩ : ∃ S : Finset R, S.card ≤ Nat.card (IsLocalRing.ResidueField R) ∧
      ∀ x : R, ∃ t ∈ S, x - t ∈ Ideal.span {ϖ} := by
    letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
    obtain ⟨sec, hsec⟩ := (IsLocalRing.residue_surjective (R := R)).hasRightInverse
    refine ⟨Finset.univ.image sec, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card]
      exact Finset.card_image_le.trans (by simp)
    · intro x
      refine ⟨sec (IsLocalRing.residue R x), by simp, ?_⟩
      rw [← hϖ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff, map_sub, hsec, sub_self]
  induction k with
  | zero =>
    refine ⟨{0}, by simp, fun x => ⟨0, by simp, by simp⟩⟩
  | succ k ih =>
    obtain ⟨S, hS, hS'⟩ := ih
    refine ⟨Finset.image₂ (fun t s => t + ϖ ^ k * s) S S₁, ?_, ?_⟩
    · refine Finset.card_image₂_le _ _ _ |>.trans ?_
      rw [pow_succ]
      exact Nat.mul_le_mul hS hS₁
    · intro x
      obtain ⟨t, ht, hx⟩ := hS' x
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      obtain ⟨s, hs, hy'⟩ := hS₁' y
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hy'
      refine ⟨t + ϖ ^ k * s, Finset.mem_image₂_of_mem ht hs, ?_⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨z, ?_⟩
      linear_combination hy + ϖ ^ k * hz

end Reps

section Main

theorem map_mul_diagonal {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (e : Fin n → K) (X Y : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f (X i j) * e j = e i * f (Y i j)) :
    X.map f * Matrix.diagonal e = Matrix.diagonal e * Y.map f := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact h i j

end Main

section Cover

theorem double_coset_cover : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m →
    ∀ [Finite (IsLocalRing.ResidueField R)] (lam : Fin n → ℤ), Antitone lam →
    ∃ s : Finset (Matrix (Fin n) (Fin n) K),
      s.card ≤ Nat.card (IsLocalRing.ResidueField R) ^
        (∑ i : Fin n, ∑ j : Fin n, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ (A1 A2 : Matrix (Fin n) (Fin n) R),
        (∀ i j, A1 i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
        (∀ i j, A2 i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
        ∃ g ∈ s, ∃ B : Matrix (Fin n) (Fin n) R,
          (∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
          A1.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (lam i)) *
            A2.map (algebraMap R K) = g * B.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ m hϖ hm _ lam hlam
  classical
  choose reps hcard hrep using fun k => exists_reps R hϖ k
  set a := algebraMap R K with ha
  set J : Ideal R := Ideal.span {ϖ ^ m} with hJ
  have hπ : a ϖ ≠ 0 := by
    intro h
    have h0 : ϖ = 0 := (IsFractionRing.injective R K) (by rw [map_zero]; exact h)
    exact hϖ.ne_zero h0

  have hpow : ∀ i j : Fin n, j ≤ i → a ϖ ^ lam i * a ϖ ^ (lam j - lam i).toNat = a ϖ ^ lam j := by
    intro i j h
    have h0 : 0 ≤ lam j - lam i := sub_nonneg.mpr (hlam h)
    rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_add₀ hπ]
    congr 1
    ring
  let Tf : Fin n → Fin n → Finset R := fun i j =>
    if i < j then (reps (lam i - lam j).toNat).image (fun x => ϖ ^ m * x)
    else {(1 : Matrix (Fin n) (Fin n) R) i j}
  let S : Finset (Fin n → Fin n → R) :=
    Fintype.piFinset fun i => Fintype.piFinset fun j => Tf i j
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i => a ϖ ^ (lam i))
  let f : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) K :=
    fun r => (Matrix.of r).map a * D
  have hT : ∀ i j, (Tf i j).card ≤ Nat.card (IsLocalRing.ResidueField R) ^
      (if i < j then (lam i - lam j).toNat else 0) := by
    intro i j
    by_cases h : i < j
    · simp only [Tf, if_pos h]
      exact Finset.card_image_le.trans (hcard _)
    · simp [Tf, if_neg h]
  refine ⟨S.image f, ?_, ?_⟩
  · calc (S.image f).card ≤ S.card := Finset.card_image_le
      _ = ∏ i, ∏ j, (Tf i j).card := by simp [S, Fintype.card_piFinset]
      _ ≤ ∏ i : Fin n, ∏ j : Fin n, Nat.card (IsLocalRing.ResidueField R) ^
            (if i < j then (lam i - lam j).toNat else 0) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ =>
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun j _ => hT i j
      _ = _ := by simp only [Finset.prod_pow_eq_pow_sum]
  · intro A1 A2 h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hul, hud, hdo, hlu, hld, hA⟩ :=
      GlobalTheory.CompanionTheory.IwahoriUDL.iwahori_udl R n ϖ m hϖ hm A1 h1
    have hdec : ∀ i j : Fin n, i < j → ∀ c ∈ J, ∃ t v : R,
        t ∈ (fun x => ϖ ^ m * x) '' (reps (lam i - lam j).toNat : Set R) ∧
        v ∈ (Ideal.span {ϖ ^ (m + (lam i - lam j).toNat)} : Set R) ∧
        t ∈ J ∧ v ∈ J ∧ c = t + v := by
      intro i j _ c hc
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hc
      obtain ⟨t, ht, hy⟩ := hrep (lam i - lam j).toNat y
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hy
      refine ⟨ϖ ^ m * t, ϖ ^ (m + (lam i - lam j).toNat) * z, ⟨t, ht, rfl⟩, ?_, ?_, ?_, ?_⟩
      · exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
      · exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
      · exact Ideal.mem_span_singleton.mpr ⟨ϖ ^ (lam i - lam j).toNat * z, by ring⟩
      · rw [pow_add]
        linear_combination ϖ ^ m * hz
    obtain ⟨r, w, hrl, hrd, hrT, hwl, hwd, hwV, huw⟩ := solve_unitriangular J
      (fun i j => (fun x => ϖ ^ m * x) '' (reps (lam i - lam j).toNat : Set R))
      (fun i j => (Ideal.span {ϖ ^ (m + (lam i - lam j).toNat)} : Set R))
      hdec u hu hul hud

    have hw' : ∀ i j, ∃ y : R, y - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J ∧
        a (w i j) * a ϖ ^ lam j = a ϖ ^ lam i * a y := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (hwV i j h)
        refine ⟨ϖ ^ m * z, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_lt h), sub_zero]
          exact Ideal.mem_span_singleton.mpr (Dvd.intro _ rfl)
        · have h0 : 0 ≤ lam i - lam j := sub_nonneg.mpr (hlam h.le)
          have e : a ϖ ^ lam j * a ϖ ^ (lam i - lam j).toNat = a ϖ ^ lam i := by
            rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← zpow_add₀ hπ]
            congr 1
            ring
          rw [hz, pow_add, ← e]
          simp only [map_mul, map_pow]
          ring
      · subst h
        refine ⟨1, by simp [J.zero_mem], ?_⟩
        rw [hwd]
        simp [mul_comm]
      · refine ⟨0, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_gt h)]
          simp
        · rw [hwl i j h]
          simp
    have hl' : ∀ i j, ∃ y : R, y - (1 : Matrix (Fin n) (Fin n) R) i j ∈ J ∧
        a (l i j) * a ϖ ^ lam j = a ϖ ^ lam i * a y := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · refine ⟨0, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_lt h)]
          simp
        · rw [hlu i j h]
          simp
      · subst h
        refine ⟨1, by simp [J.zero_mem], ?_⟩
        rw [hld]
        simp [mul_comm]
      · refine ⟨l i j * ϖ ^ (lam j - lam i).toNat, ?_, ?_⟩
        · rw [Matrix.one_apply_ne (ne_of_gt h), sub_zero]
          have := hl i j
          rw [Matrix.one_apply_ne (ne_of_gt h), sub_zero] at this
          exact J.mul_mem_right _ this
        · rw [← hpow i j h.le]
          simp only [map_mul, map_pow]
          ring
    choose w' hw'1 hw'2 using hw'
    choose l' hl'1 hl'2 using hl'
    have ew : (w.map a) * D = D * (Matrix.of w').map a :=
      map_mul_diagonal a _ w (Matrix.of w') hw'2
    have el : (l.map a) * D = D * (Matrix.of l').map a :=
      map_mul_diagonal a _ l (Matrix.of l') hl'2
    have ed : (d.map a) * D = D * d.map a := by
      refine map_mul_diagonal a _ d d fun i j => ?_
      by_cases h : i = j
      · subst h
        exact mul_comm _ _
      · rw [hdo i j h]
        simp
    refine ⟨f r, Finset.mem_image_of_mem f ?_, Matrix.of w' * d * Matrix.of l' * A2, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mpr fun j => ?_
      by_cases h : i < j
      · simp only [Tf, if_pos h]
        obtain ⟨t, ht, e⟩ := hrT i j h
        exact Finset.mem_image.mpr ⟨t, ht, e⟩
      · simp only [Tf, if_neg h, Finset.mem_singleton]
        rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
        · rw [hrl i j h', Matrix.one_apply_ne (ne_of_gt h')]
        · subst h'
          rw [hrd, Matrix.one_apply_eq]
    · exact mul_congr_one (mul_congr_one (mul_congr_one hw'1 hd) hl'1) h2
    · show A1.map a * D * A2.map a = (Matrix.of r).map a * D * _
      have er : (Matrix.of r) = r := rfl
      rw [er, hA, huw]
      simp only [Matrix.map_mul]
      calc r.map a * w.map a * d.map a * l.map a * D * A2.map a
          = r.map a * w.map a * d.map a * (l.map a * D) * A2.map a := by
            simp only [Matrix.mul_assoc]
        _ = r.map a * w.map a * (d.map a * D) * (Matrix.of l').map a * A2.map a := by
            rw [el]
            simp only [Matrix.mul_assoc]
        _ = r.map a * (w.map a * D) * d.map a * (Matrix.of l').map a * A2.map a := by
            rw [ed]
            simp only [Matrix.mul_assoc]
        _ = r.map a * D * ((Matrix.of w').map a * d.map a * (Matrix.of l').map a * A2.map a) := by
            rw [ew]
            simp only [Matrix.mul_assoc]

end Cover

end GlobalTheory.CompanionTheory.KmCover
