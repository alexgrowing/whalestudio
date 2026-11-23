import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.LeSuccIff

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.LocB

open ValuativeRel GlobalTheory.WeilM GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {ϖ : kˣ}
  {ξ : kˣ →* ℂˣ} {ψ : AddChar k ℂ} {c : ℤ} {l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ} {i₀ i₁ : Fin d}

def ex (a : Fin n) (i : Fin d) (p : ℤ) (T : Finset (Fin n)) (β γ : Fin d → ℤ) : Fin n → Fin d → ℤ :=
  fun x y => if y = i then (if x = a ∨ x ∈ T then p else p + 1) else if x = a then β y else γ y

def val (ϖ : kˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) (a : Fin n) (i : Fin d) (p : ℤ) (T : Finset (Fin n))
    (β γ : Fin d → ℤ) : ℂ := l ((Piv ϖ a i (ex a i p T β γ)).indicator 1)

theorem what₂ (h : IsUnif ϖ) (hl : LeftLaw ξ l) (a : Fin n) (i : Fin d) (p : ℤ) (β γ : Fin d → ℤ) (hb : ∀ y, γ y ≤ β y)
    (T : Finset (Fin n)) (hT : a ∉ T) :
    val ϖ l a i p T β γ = (GlobalTheory.SplitWeil.resCard k : ℂ) ^ T.card * val ϖ l a i p ∅ β γ := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a' T ha ih =>
    rw [Finset.mem_insert, not_or] at hT
    have hT1 : a' ≠ a := fun e => hT.1 e.symm
    rw [Finset.card_insert_of_notMem ha, pow_succ', mul_assoc, ← ih hT.2]
    refine move h l a i _ _ a' i (fun e => hT.1 e.1) ?_ (fun Y => Matrix.of fun x y => if x = a' then Y a y else 0)
      (by simp) (by simp [hT.1]) (fun t Y => by ext x y; simp [hT.1]) ?_ ?_
    · intro x y
      by_cases hx : x = a' <;> by_cases hy : y = i <;> simp [ex, hx, hy, ha, hT1]
    · intro Y hY x y
      by_cases hx : x = a'
      · simp only [Matrix.of_apply, if_pos hx]
        refine (hY a y).mono h ?_
        by_cases hy : y = i <;> simp [ex, hx, hy, hT1, hb]
      · simpa [hx] using Le.zero _
    · intro t _
      have hd : (Matrix.transvection a' a t).det = 1 := Matrix.det_transvection_of_ne _ _ hT1 _
      have := hl _ (piv_SB h a i (ex a i p T β γ))
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection a' a t) (by rw [hd]; exact one_ne_zero))
      rw [show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection a' a t)
        (by rw [hd]; exact one_ne_zero)) = 1 from Units.ext hd, map_one, Units.val_one, one_mul] at this
      rw [← this]
      congr 1
      funext Y
      congr 1
      ext x y
      show _ = (Matrix.transvection a' a t * Y) x y
      by_cases hx : x = a'
      · subst hx; simp
      · simp [hx]

theorem colOp_single (i j : Fin d) (t : k) (Y : Matrix (Fin n) (Fin d) k) :
    colOp i (Pi.single j t) Y = Y + t • Matrix.of fun x y => if y = j then Y x i else 0 := by
  ext x y
  by_cases hy : y = j <;> simp [colOp, Matrix.vecMulVec_apply, hy, mul_comm]

theorem cols (h : IsUnif ϖ) (hψ : ∀ x, Le ϖ c x → ψ x = 1) (hl : ColLaw ψ {i₀} i₀ i₁ l) (a : Fin n) (p : ℤ) (β γ : Fin d → ℤ)
    (hb : ∀ y, γ y ≤ β y) (hc : c ≤ β i₁ - 1 - p) (U : Finset (Fin d)) (hU : i₀ ∉ U) :
    val ϖ l a i₀ p ∅ (fun y => β y - if y ∈ U then 1 else 0) γ =
      (GlobalTheory.SplitWeil.resCard k : ℂ) ^ U.card * val ϖ l a i₀ p ∅ β γ := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert j U hj ih =>
    rw [Finset.mem_insert, not_or] at hU
    have hU1 : j ≠ i₀ := fun e => hU.1 e.symm
    rw [Finset.card_insert_of_notMem hj, pow_succ', mul_assoc, ← ih hU.2]
    refine move h l a i₀ _ _ a j (fun e => hU.1 e.2) ?_ (fun Y => Matrix.of fun x y => if y = j then Y x i₀ else 0)
      (by simp) (by simp [hU.1]) (fun t Y => by ext x y; simp [hU.1]) ?_ ?_
    · intro x y
      by_cases hx : x = a <;> by_cases hy : y = j <;> simp [ex, hx, hy, hj, hU1]
    · intro Y hY x y
      by_cases hy : y = j
      · simp only [Matrix.of_apply, if_pos hy]
        refine (hY x i₀).mono h ?_
        have := hb j
        by_cases hx : x = a <;> simp [ex, hx, hy, hU1]
        omega
      · simpa [hy] using Le.zero _
    · intro t ht
      have := hl _ (piv_SB h a i₀ (ex a i₀ p ∅ (fun y => β y - if y ∈ U then 1 else 0) γ)) (Pi.single j t)
        (by rintro s rfl; simp [hU.1])
      simp only [colOp_single] at this
      rw [this, hψ, one_mul]
      by_cases e : i₁ = j
      · subst e
        rw [Pi.single_eq_same]
        exact ht.mono h (by simpa [ex, hU1] using hc)
      · simpa [e] using Le.zero _

theorem scale (h : IsUnif ϖ) (hl : LeftLaw ξ l) (a : Fin n) (i : Fin d) (p : ℤ) (β γ : Fin d → ℤ) :
    val ϖ l a i p ∅ β γ = ξ ϖ * val ϖ l a i (p + 1) (Finset.univ.erase a) (fun y => β y + 1) γ := by
  have hd : (Matrix.diagonal (Function.update (1 : Fin n → k) a ϖ)).det = ϖ := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  have := hl _ (piv_SB h a i (ex a i (p + 1) (Finset.univ.erase a) (fun y => β y + 1) γ))
    (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hd]; exact ϖ.ne_zero))
  rw [show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal (Function.update (1 : Fin n → k) a ϖ)) (by rw [hd]; exact ϖ.ne_zero)) = ϖ from Units.ext hd] at this
  unfold val
  rw [← this]
  congr 1
  funext Y
  refine Set.indicator_eq_indicator ?_ rfl
  show _ ↔ Matrix.diagonal (Function.update (1 : Fin n → k) a ϖ) * Y ∈ _
  have hv : valuation k (ϖ : k) = valuation k (ϖ : k) ^ (1 : ℤ) := (zpow_one _).symm
  refine and_congr (forall₂_congr fun x y => ?_) ?_
  · rw [Matrix.diagonal_mul]
    by_cases hx : x = a
    · subst hx
      rw [Function.update_self, mul_comm, ← le_mul_iff hv]
      by_cases hy : y = i <;> simp [ex, hy]
    · by_cases hy : y = i <;> simp [ex, hy, hx]
  · simp only [ex, Matrix.diagonal_mul, Function.update_self, map_mul, true_or, if_true]
    rw [zpow_add_one₀ (u_pos ϖ).ne', mul_comm, mul_left_inj' (u_pos ϖ).ne']

theorem trace (h : IsUnif ϖ) (hi : i₀ ≠ i₁) (a : Fin n) (p : ℤ) (β γ γ' : Fin d → ℤ) (h1 : ∀ y, y ≠ i₁ → γ' y = γ y)
    (h2 : γ' i₁ ≤ β i₁ + 1) (Y : Matrix (Fin n) (Fin d) k) (hY : ¬ LinearIndependent k ![fun a => Y a i₀, fun a => Y a i₁])
    (hm : Y ∈ Piv ϖ a i₀ (ex a i₀ p ∅ β γ)) : Y ∈ Piv ϖ a i₀ (ex a i₀ p ∅ β γ') := by
  obtain ⟨hb, hp⟩ := hm
  have hp' : valuation k (Y a i₀) = valuation k (ϖ : k) ^ p := by simpa [ex] using hp
  have h0 : (fun a => Y a i₀) ≠ 0 := fun e => by
    rw [show Y a i₀ = 0 from congrFun e a, map_zero] at hp'
    exact (zpow_pos (u_pos ϖ) _).ne hp'
  rw [LinearIndependent.pair_iff' h0] at hY
  push Not at hY
  obtain ⟨s, hs⟩ := hY
  have hs' : ∀ x, s * Y x i₀ = Y x i₁ := congrFun hs
  refine ⟨fun x y => ?_, by simpa [ex] using hp⟩
  by_cases hx : x = a
  · simpa [ex, hx] using hb x y
  by_cases hy : y = i₁
  · subst hy
    have h3 : Le ϖ (β y - p) s := by
      rw [← le_mul_iff hp', hs', sub_add_cancel]
      simpa [ex, hi.symm] using hb a y
    have h4 : Le ϖ (p + 1) (Y x i₀) := by simpa [ex, hx] using hb x i₀
    rw [← hs']
    refine (h3.mul h4).mono h ?_
    simp [ex, hx, hi.symm]
    omega
  · simpa [ex, h1 y hy] using hb x y

def bs (i₁ : Fin d) (μ : ℤ) : Fin d → ℤ := fun y => if y = i₁ then μ else 0

theorem ex_congr (a : Fin n) (i : Fin d) (p : ℤ) (T : Finset (Fin n)) {β β' : Fin d → ℤ} (γ : Fin d → ℤ)
    (hb : ∀ y, y ≠ i → β y = β' y) : val ϖ l a i p T β γ = val ϖ l a i p T β' γ := by
  have : ex a i p T β γ = ex a i p T β' γ := by
    funext x y
    by_cases hy : y = i
    · simp [ex, hy]
    · simp [ex, hy, hb y hy]
  rw [val, val, this]

theorem q_ne : (GlobalTheory.SplitWeil.resCard k : ℂ) ≠ 0 := by
  have : 0 < GlobalTheory.SplitWeil.resCard k := Nat.card_pos
  exact_mod_cast this.ne'

theorem stepA (h : IsUnif ϖ) (hψ : ∀ x, Le ϖ c x → ψ x = 1) (hl : LeftLaw ξ l) (hl' : ColLaw ψ {i₀} i₀ i₁ l) (a : Fin n)
    (p μ : ℤ) (hc : c ≤ μ - 1 - p) : val ϖ l a i₀ p ∅ (bs i₁ μ) (bs i₁ μ) =
      ξ ϖ * (GlobalTheory.SplitWeil.resCard k : ℂ) ^ ((n : ℤ) - d) * val ϖ l a i₀ (p + 1) ∅ (bs i₁ μ) (bs i₁ μ) := by
  have h1 := cols h hψ hl' a (p + 1) (fun y => bs i₁ μ y + 1) (bs i₁ μ) (fun y => by omega) (by simp [bs]; omega)
    (Finset.univ.erase i₀) (by simp)
  rw [ex_congr (β' := bs i₁ μ) a i₀ _ _ _ (fun y hy => by simp [hy])] at h1
  rw [scale h hl, what₂ h hl a i₀ _ _ _ (fun y => by omega) _ (by simp), h1]
  have hn : (n : ℤ) = ((Finset.univ.erase a).card : ℕ) + 1 := by
    have := Finset.card_erase_add_one (Finset.mem_univ a)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hd : (d : ℤ) = ((Finset.univ.erase i₀).card : ℕ) + 1 := by
    have := Finset.card_erase_add_one (Finset.mem_univ i₀)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [hn, hd, add_sub_add_right_eq_sub, zpow_sub₀ q_ne, zpow_natCast, zpow_natCast]
  have := pow_ne_zero (Finset.univ.erase i₀).card (q_ne (k := k))
  field_simp

theorem stepB (h : IsUnif ϖ) (hi : i₀ ≠ i₁) (hψ : ∀ x, Le ϖ c x → ψ x = 1) (hl' : ColLaw ψ {i₀} i₀ i₁ l)
    (hs : ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y, ¬ LinearIndependent k ![fun a => Y a i₀, fun a => Y a i₁] → φ Y = 0) → l φ = 0) (a : Fin n)
    (p μ : ℤ) (hc : c ≤ μ - p) : val ϖ l a i₀ p ∅ (bs i₁ μ) (bs i₁ μ) =
      (GlobalTheory.SplitWeil.resCard k : ℂ) * val ϖ l a i₀ p ∅ (bs i₁ (μ + 1)) (bs i₁ (μ + 1)) := by
  have h1 := cols h hψ hl' a p (bs i₁ (μ + 1)) (bs i₁ (μ + 1)) (fun y => le_rfl) (by simpa [bs] using hc) {i₁} (by simpa using hi)
  rw [ex_congr (β' := bs i₁ μ) a i₀ _ _ _ (fun y _ => by by_cases hy : y = i₁ <;> simp [bs, hy]),
    Finset.card_singleton, pow_one] at h1
  rw [← h1, ← sub_eq_zero, val, val, ← map_sub]
  refine hs _ (Submodule.sub_mem _ (piv_SB h _ _ _) (piv_SB h _ _ _)) fun Y hY => ?_
  rw [Pi.sub_apply, sub_eq_zero]
  exact Set.indicator_eq_indicator
    ⟨trace h hi a p _ _ _ (fun y hy => by simp [bs, hy]) (by simp [bs]) Y hY,
      trace h hi a p _ _ _ (fun y hy => by simp [bs, hy]) (by simp [bs]) Y hY⟩ rfl

def bx (ϖ : kˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) (i₀ i₁ : Fin d) (T : Finset (Fin n)) (p μ : ℤ) : ℂ :=
  l ((Box ϖ fun x y => if y = i₀ then (if x ∈ T then p else p + 1) else bs i₁ μ y).indicator 1)

theorem bx_insert (h : IsUnif ϖ) (hl : LeftLaw ξ l) (a : Fin n) (T : Finset (Fin n)) (ha : a ∉ T) (p μ : ℤ) :
    bx ϖ l i₀ i₁ (insert a T) p μ = bx ϖ l i₀ i₁ T p μ +
      (GlobalTheory.SplitWeil.resCard k : ℂ) ^ T.card * val ϖ l a i₀ p ∅ (bs i₁ μ) (bs i₁ μ) := by
  rw [← what₂ h hl a i₀ p _ _ (fun _ => le_rfl) T ha, val,
    piv_eq h a i₀ _ (fun x y => if y = i₀ then (if x ∈ T then p else p + 1) else bs i₁ μ y), map_sub, bx, bx, add_sub_cancel]
  · congr 3
    funext x y
    simp [ex]
  · intro x y
    by_cases hx : x = a <;> by_cases hy : y = i₀ <;> simp [ex, hx, hy, ha]

theorem bx_weights (h : IsUnif ϖ) (hl : LeftLaw ξ l) (T : Finset (Fin n)) : ∃ w : Fin n → ℂ, ∀ p μ,
    bx ϖ l i₀ i₁ T p μ - bx ϖ l i₀ i₁ ∅ p μ = ∑ a ∈ T, w a * val ϖ l a i₀ p ∅ (bs i₁ μ) (bs i₁ μ) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨Function.update w a ((GlobalTheory.SplitWeil.resCard k : ℂ) ^ T.card), fun p μ => ?_⟩
    rw [bx_insert h hl a T ha, Finset.sum_insert ha, Function.update_self, add_sub_right_comm, hw, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [Function.update_of_ne (by rintro rfl; exact ha hb)]

theorem bx_empty (p μ : ℤ) : bx ϖ l i₀ i₁ ∅ p μ = bx ϖ l i₀ i₁ Finset.univ (p + 1) μ := by simp [bx]

theorem bx_zero (h : IsUnif ϖ) (hi : i₀ ≠ i₁) (hψ : ∃ x, Le ϖ (c - 1) x ∧ ψ x ≠ 1) (hl' : ColLaw ψ {i₀} i₀ i₁ l) (p μ : ℤ)
    (hc : μ - p < c) : bx ϖ l i₀ i₁ Finset.univ p μ = 0 := by
  obtain ⟨t, ht, hne⟩ := hψ
  set e : Fin n → Fin d → ℤ := fun x y => if y = i₀ then (if x ∈ Finset.univ then p else p + 1) else bs i₁ μ y with he
  have key : ∀ t, Le ϖ (c - 1) t → ∀ Y ∈ Box ϖ e, colOp i₀ (Pi.single i₁ t) Y ∈ Box ϖ e := fun t ht Y hY x y => by
    rw [colOp_single]
    refine (hY x y).add ?_
    by_cases hy : y = i₁
    · have := (ht.mul (hY x i₀)).mono h (e' := e x y) (by simp [he, hy, hi.symm, bs]; omega)
      simpa [hy] using this
    · simpa [hy] using Le.zero _
  have := hl' _ (box_SB ϖ e) (Pi.single i₁ t) (by rintro s rfl; simp [hi])
  have h2 : (fun Y => (Box ϖ e).indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) (colOp i₀ (Pi.single i₁ t) Y)) = (Box ϖ e).indicator 1 := by
    funext Y
    refine Set.indicator_eq_indicator ⟨fun hY => ?_, key t ht Y⟩ rfl
    convert key (-t) (by simpa using (Le.zero _).sub ht) _ hY using 1
    ext x y
    simp only [colOp_single]
    by_cases hy : y = i₁ <;> simp [hy, hi]
  rw [h2, Pi.single_eq_same] at this
  by_contra h0
  exact hne (mul_right_cancel₀ h0 (this.symm.trans (one_mul _).symm))

theorem solve (B : ℤ → ℤ → ℂ) (c : ℤ) (q r : ℂ) (hq : q * r ≠ 0)
    (hA : ∀ p μ, c ≤ μ - 1 - p → B p μ - B (p + 1) μ = r * (B (p + 1) μ - B (p + 1 + 1) μ))
    (hB : ∀ p μ, c ≤ μ - p → B p μ - B (p + 1) μ = q * (B p (μ + 1) - B (p + 1) (μ + 1)))
    (h0 : ∀ p μ, μ - p < c → B p μ = 0) :
    ∃ x : ℂ, ∀ m : ℕ, B (-m) m = x * (q * r) ^ (-(m : ℤ)) * ∑ i ∈ Finset.range (2 * m - c + 1).toNat, r ^ i := by
  have h1 : ∀ μ (j : ℕ), B (μ - c - j) μ - B (μ - c - j + 1) μ = r ^ j * B (μ - c) μ := by
    intro μ j
    induction j with
    | zero => simp [h0 (μ - c + 1) μ (by omega)]
    | succ j ih =>
      rw [hA _ _ (by push_cast; omega), show μ - c - ((j + 1 : ℕ) : ℤ) + 1 = μ - c - j by push_cast; ring, ih]
      ring
  have h2 : ∀ μ (j : ℕ), B (μ - c - j + 1) μ = B (μ - c) μ * ∑ i ∈ Finset.range j, r ^ i := by
    intro μ j
    induction j with
    | zero => simp [h0 (μ - c + 1) μ (by omega)]
    | succ j ih =>
      rw [show μ - c - ((j + 1 : ℕ) : ℤ) + 1 = μ - c - j by push_cast; ring, Finset.sum_range_succ]
      linear_combination h1 μ j + ih
  have h3 : ∀ m : ℕ, B (m - c) m = B (0 - c) 0 * (q * r) ^ (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e1 := hB (m - c) m (by omega)
      have e2 := h1 (m + 1) 1
      rw [h0 (m - c + 1) m (by omega)] at e1
      rw [show (m : ℤ) + 1 - c - ((1 : ℕ) : ℤ) = m - c by push_cast; ring] at e2
      rw [e2, ih] at e1
      push_cast
      rw [neg_add, zpow_add₀ hq, ← mul_assoc, zpow_neg_one, eq_mul_inv_iff_mul_eq₀ hq]
      linear_combination -e1
  refine ⟨B (0 - c) 0, fun m => ?_⟩
  rw [← h3, ← h2]
  by_cases hm : 0 ≤ 2 * (m : ℤ) - c + 1
  · congr 1
    rw [Int.toNat_of_nonneg hm]; ring
  · rw [h0 _ _ (by omega), h0 _ _ (by omega)]

end LocB

open LocB ValuativeRel in
theorem locTwo_of (H : LocSupp) : LocTwo := by
  intro k _ _ _ _ n d ϖ h ψ c hψ hψ' i₀ i₁ hi ξ _ l hl hl' r hr
  have hψ1 : ∀ x, Le ϖ c x → ψ x = 1 := fun x hx => hψ x (by simpa [Le] using hx)
  have hψ2 : ∃ x, Le ϖ (c - 1) x ∧ ψ x ≠ 1 := hψ'.imp fun x hx => ⟨by simpa [Le] using hx.1, hx.2⟩
  have hs := H k n d ψ (by rintro rfl; obtain ⟨x, -, hx⟩ := hψ2; exact hx rfl) i₀ i₁ hi ξ l hl hl'
  obtain ⟨w, hw⟩ := bx_weights (i₀ := i₀) (i₁ := i₁) h hl Finset.univ
  simp only [bx_empty] at hw
  obtain ⟨x, hx⟩ := solve (bx ϖ l i₀ i₁ Finset.univ) c (GlobalTheory.SplitWeil.resCard k) r
    (mul_ne_zero q_ne (hr ▸ mul_ne_zero (ξ ϖ).ne_zero (zpow_ne_zero _ q_ne)))
    (fun p μ hc => by
      rw [hw, hw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [stepA h hψ1 hl hl' a p μ hc, hr]; ring)
    (fun p μ hc => by
      rw [hw, hw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [stepB h hi hψ1 hl' hs a p μ hc]; ring)
    (bx_zero h hi hψ2 hl')
  refine ⟨x, fun m => ?_⟩
  rw [← hx, bx]
  congr 1
  funext Y
  refine Set.indicator_eq_indicator (forall₂_congr fun a b => ?_) rfl
  rw [torus, Matrix.mul_diagonal, ← le_zero_iff (ϖ := ϖ)]
  by_cases h0 : b = i₀
  · simp only [if_pos h0, Finset.mem_univ, if_true]
    rw [← le_mul_iff (e := -(m : ℤ)) (val_zpow m), neg_add_cancel, zpow_natCast]
  · by_cases h1 : b = i₁
    · simp only [if_neg h0, bs, if_pos h1]
      rw [← le_mul_iff (e := (m : ℤ)) (val_zpow (-m)), add_neg_cancel, zpow_neg, zpow_natCast]
    · simp [h0, h1, bs]

end PositivityTheory.ThKEnd.Cusp

end
