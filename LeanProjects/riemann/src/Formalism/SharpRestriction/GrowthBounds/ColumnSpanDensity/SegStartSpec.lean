import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InitialLevelFormula

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem posAdd_cdist {n' : ℕ} (x y : Fin n') : posAdd x (cdist x y) = y := by
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod]
  have h : x.val + (y.val + n' - x.val) = y.val + n' := by
    have := x.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

theorem mem_segDists {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (d : ℕ) :
    d ∈ segDists TT j ↔ ∃ s ∈ TT, ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j ∧ cdist (segStart TT j) s = d := by
  unfold segDists
  rw [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩
  · rintro ⟨s, hs, h1, h2, h3, rfl⟩
    exact ⟨s, Finset.mem_filter.2 ⟨hs, h1, h2, h3⟩, rfl⟩

theorem segPos_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧ 0 < (segDists TT j).get i ∧
      (segDists TT j).get i < segG TT j := by
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := (mem_segDists TT j _).1 (List.get_mem (segDists TT j) i)
  have e : segPos TT j i = s := by
    unfold segPos
    rw [← h4]
    exact posAdd_cdist _ _
  rw [e]
  exact ⟨hs, h1, h4, h4 ▸ h2, h4 ▸ h3⟩

theorem mem_evenTops {n' : ℕ} (TT : Finset (Fin n')) (x : Fin n') : x ∈ evenTops TT ↔ x ∈ TT ∧ Even x.val := by
  unfold evenTops
  rw [Finset.mem_sort, Finset.mem_filter]

theorem segStart_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segStart TT j ∈ TT ∧ Even (segStart TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

theorem ex_cast {n' : ℕ} {TT : Finset (Fin n')} (z : Fin n' → ℤ) (c : ℕ) (s : Fin n') (hs : s ∈ TT) (h0 : 0 ≤ z s) :
    ((ex (TT := TT) (fun s => (z s + c).toNat) s : ℕ) : ℝ) = (z s : ℝ) + c := by
  unfold ex
  rw [dif_pos hs]
  have h : ((z s + c).toNat : ℤ) = z s + c := Int.toNat_of_nonneg (by positivity)
  have h' : (((z s + c).toNat : ℤ) : ℝ) = ((z s + c : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem min_shift (b a c P : ℝ) (hc : 0 ≤ c) (hP : 1 ≤ P) : min (b + c) ((a + c) / P) ≤ min b (a / P) + c := by
  have hP0 : 0 < P := by linarith
  have h1 : c / P ≤ c := div_le_self hc hP
  have h2 : (a + c) / P = a / P + c / P := add_div _ _ _
  rw [← min_add_add_right]
  exact min_le_min le_rfl (by rw [h2]; linarith)

open Classical in
theorem tle_of (hO : RestOddTops) {K : Cst} (hK : K.Pos) {CH : ℝ} {C : ℝ} (hC : 4 * K.Ct + 4 ≤ C)
    {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) (aw bw : Fin X.n' → ℤ)
    (hw : ∀ s ∈ X.TT, aw s ∈ IaZ X.m X.Y X.ar ∧ bw s ∈ IbZ X.bl X.bu) :
    (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) + 2 * X.n' * X.ccl ≤
      tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw := by
  have hseg2 : 2 ≤ numSeg X.TT := h.2.2.2.1
  have hbl : 0 ≤ X.bl := by
    have := lowb_of h
    linarith [B.hb8]
  have hp1 : (1 : ℝ) ≤ X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have ha0 : ∀ s ∈ X.TT, 0 ≤ aw s := fun s hs =>
    le_trans (Int.ceil_nonneg (by linarith)) (Finset.mem_Icc.1 (hw s hs).1).1
  have hb0 : ∀ s ∈ X.TT, 0 ≤ bw s := fun s hs =>
    le_trans (Int.ceil_nonneg hbl) (Finset.mem_Icc.1 (hw s hs).2).1
  set S : ℝ := ∑ y ∈ X.TT.filter (fun y => ¬ IsTypeV y),
      min (bw y : ℝ) ((aw (yPrev X.TT y) : ℝ) / (X.p : ℝ) ^ dPrev X.TT y) with hS
  set S' : ℝ := ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex (TT := X.TT) (fun s => (bw s + X.ccl).toNat) (segPos X.TT j i) : ℕ) : ℝ)
          (((ex (TT := X.TT) (fun s => (aw s + X.ccl).toNat) (segStart X.TT j) : ℕ) : ℝ) /
            (X.p : ℝ) ^ ((segDists X.TT j).get i)) with hS'
  have hcount : (∑ j : Fin (numSeg X.TT), ∑ _i : Fin (segS X.TT j), (X.ccl : ℝ)) ≤ X.N * X.ccl := by
    have := hO X.n' X.TT hseg2 (fun _ _ _ => (X.ccl : ℝ))
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold Dat.N
    exact_mod_cast Finset.card_filter_le _ _
  have hSS : S' ≤ S + X.N * X.ccl := by
    have e := hO X.n' X.TT hseg2 (fun y x d => min (bw y : ℝ) ((aw x : ℝ) / (X.p : ℝ) ^ d))
    have h1 : S' ≤ ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        (min (bw (segPos X.TT j i) : ℝ) ((aw (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i)) +
          (X.ccl : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      rw [ex_cast bw X.ccl _ (segPos_spec X.TT j i).1 (hb0 _ (segPos_spec X.TT j i).1),
        ex_cast aw X.ccl _ (segStart_spec X.TT j).1 (ha0 _ (segStart_spec X.TT j).1)]
      exact min_shift _ _ _ _ (by positivity) (one_le_pow₀ hp1)
    simp only [Finset.sum_add_distrib] at h1
    rw [e] at h1
    linarith
  have hS'0 : 0 ≤ S' := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact le_min (by positivity) (by positivity)

  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hlog0 : 0 ≤ Real.log X.a := Real.log_nonneg ha1
  have hlog2 : Real.log X.a ≤ 2 * Real.log X.ar := by
    have h10 : (X.a : ℝ) ≤ X.ar ^ 2 := by
      have : 2 * X.ar ≤ X.ar * X.ar := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e : X.ar ^ 2 = X.ar * X.ar := by ring
      rw [e]
      linarith [B.haa1]
    have := Real.log_le_log (by linarith) h10
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by unfold LaI; exact mul_nonneg hcn hlog0
  have hLa'2 : LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar := by
    unfold LaI
    have := mul_le_mul_of_nonneg_left hlog2 hcn
    linarith
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hb : 0 < X.b' := by linarith [B.hb8]
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hJ : X.J0 K = LaI K.C₀ X.N₁ X.a * X.b' / X.k := rfl
  have key := tle_abs K.Ct C X.N X.N₁ X.p X.k ((X.p : ℝ) ^ X.G') (Real.logb X.p X.ar) X.ar X.a X.b'
    (LaI K.C₀ X.N₁ X.ar) (LaI K.C₀ X.N₁ X.a) X.ccl X.cStar X.n' S S' hK.2.2.2.2.2.2.2.1 hC (by linarith [B.hN2])
    B.hN1 hp0 hk1 B.hQ (by linarith [B.hL1]) (by linarith) (by linarith) (by linarith [B.haa1]) hb
    (by linarith [B.hLa1]) hLa'0 hLa'2 (by positivity) (by positivity) (by positivity) hSS
  have hx0 : 0 ≤ X.t0 K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) + X.N * X.J0 K := by
    rw [initial_level_formula, hJ]
    have hCt : 0 < K.Ct := hK.2.2.2.2.2.2.2.1
    have hk0 : 0 < X.k := by linarith
    have hQ0 : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by positivity
    have := hS'0
    positivity
  have hceil : (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) ≤
      (S' + K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl))) +
        X.N * (LaI K.C₀ X.N₁ X.a * X.b' / X.k) + 1 := by
    have h1 := (Nat.ceil_lt_add_one hx0).le
    have h2 := initial_level_formula K X (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat)
    unfold Dat.tStar
    calc _ ≤ _ := h1
      _ = _ := by rw [h2, hJ]
  have htI : tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw =
      S + C * X.N * X.N₁ * (X.ar / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.ar * X.ar / (X.p * X.k) +
          LaI K.C₀ X.N₁ X.ar * X.b' / X.k) +
        C * X.N * ((X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + C * X.N * X.k * Real.logb X.p X.ar + 4 * X.N * X.ccl +
          2 * X.n' * X.ccl) + X.k * (X.p : ℝ) ^ X.G' + X.k * Real.logb X.p X.ar + X.ccl) + 2 * X.n' * X.ccl := rfl
  rw [htI]
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
