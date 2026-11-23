import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementG
import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementF
import Formalism.ThetaLogCoordinates.FockResolutionOnto.MulEarlyModP
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalM

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem resSatL_mono (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    {c c' : ℕ} (hc : c ≤ c') (h : ResSatL p LL J M ρ c) : ResSatL p LL J M ρ c' := by
  unfold ResSatL at h ⊢
  intro x hx hxI
  obtain ⟨g, hgY, hgI, hge⟩ := h x hx hxI
  refine ⟨((p : ℚ_[p]) ^ (c' - c)) • g, Submodule.smul_mem _ _ hgY, ?_, ?_⟩
  · have e : ((p : ℚ_[p]) ^ (c' - c)) • g = ((p : ℤ_[p]) ^ (c' - c)) • g := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ (c' - c)) g]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ hgI
  · have hl : initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (c' - c)) • g)
        = ((p : ℚ_[p]) ^ (c' - c)) • initPart (Fin.last K, ρ) 0 g :=
      (resL p (Fin.last K, ρ) 0).map_smul _ g
    rw [hl, hge, smul_smul, ← pow_add, Nat.sub_add_cancel hc]

theorem resOntoK_of_resSatL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (c0 : ℕ) (h : ResSatL p LL J M ρ c0) : ResOntoK p LL J M ρ := by
  classical
  unfold ResOntoK
  unfold ResSatL at h
  intro x hx
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ_[p])
    (x.support.image fun m => MvPolynomial.coeff m x)
  have hb' : ∀ m, ∃ y : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] y = (b : ℤ_[p]) • MvPolynomial.coeff m x := by
    intro m
    by_cases hm : m ∈ x.support
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_image_of_mem _ hm)
      exact ⟨y, hy⟩
    · refine ⟨0, ?_⟩
      have h0 : MvPolynomial.coeff m x = 0 := by
        by_contra hne
        exact hm (MvPolynomial.mem_support_iff.2 hne)
      rw [h0, smul_zero, map_zero]
  choose y hy using hb'
  have hbx : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) • x ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine LinearMap.mem_range.2 ⟨∑ m ∈ x.support, monomial m (y m), ?_⟩
    change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (∑ m ∈ x.support, monomial m (y m)) = _
    rw [map_sum]
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hy m, MvPolynomial.smul_monomial]
    congr 1
  obtain ⟨g, hgY, hgI, hge⟩ := h _ (Submodule.smul_mem _ _ hx) hbx
  have hs0 : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hp0 : ((p : ℚ_[p]) ^ c0) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine ⟨((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ • g, Submodule.smul_mem _ _ hgY, ?_⟩
  rw [initPart_smul, hge, smul_smul, smul_smul]
  have h1 : ((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ * (p : ℚ_[p]) ^ c0
      * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) = 1 := by
    field_simp
  rw [h1, one_smul]

theorem resMMZL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 c0 : ℕ) (hHP : HypP p LL ρ e1) (hHE : HypE p LL ρ e1) (hSat : ResSatL p LL J M ρ c0)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ XH p LL J M ρ w)
    (hxI : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ MMwZ p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ (e1 + c0)) • x := by
  obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
  obtain ⟨h0, hh0, hh0I, hres⟩ := hSat x hxX hxI
  obtain ⟨PE, hPE, -, hInt⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
  have hY := wtComp_Y LL J M w h0 hh0
  have hW := wtComp_mem (p := p) LL (K + 1) w h0
  refine ⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr
    ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW),
      hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩
  change resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _
  change resL p (Fin.last K, ρ) 0 h0 = _ at hres
  rw [map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres,
    wtComp_fix LL (K + 1) w _ (Submodule.smul_mem _ _ hxW), map_smul,
    eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩), smul_smul, ← pow_add]

theorem satAtL (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 c0 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hS : ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) :
    SatAt p LLw J M ρ w e (e1 + c0) := by
  intro x hx hxI
  obtain ⟨y, hy, rfl⟩ :=
    (grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 hS) x).mp hx
  rw [pow_mul_int_iff] at hxI
  obtain ⟨h, hh, hres⟩ := resMMZL (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 c0 hP hE hS y hy hxI
  refine (graded_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, ?_⟩
  rw [hres, mul_smul_comm]

theorem setLast_deg_last (LL : Letters (K + 1)) (o : ℕ) : (setLast LL o).deg (Fin.last K) = o := by
  simp [setLast]

theorem setLast_setLast (LL : Letters (K + 1)) (a b : ℕ) : setLast (setLast LL a) b = setLast LL b := by
  simp [setLast]

theorem setLast_total_le (LL : Letters (K + 1)) (o : ℕ) (ho : o ≤ LL.deg (Fin.last K)) :
    (setLast LL o).total ≤ LL.total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = Fin.last K
  · subst hi
    simpa [setLast] using ho
  · simp [setLast, Function.update_of_ne hi]

theorem shiftLastLetterThresholds_add {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (a b : ℕ) :
    shiftLastLetterThresholds K J (shiftLastLetterThresholds K J M a) b = shiftLastLetterThresholds K J M (a + b) := by
  funext k
  by_cases h : K + 1 ≤ J k
  · simp only [shiftLastLetterThresholds, h, ↓reduceIte]
    rw [add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring
  · simp only [shiftLastLetterThresholds, h, ↓reduceIte]

end Last

theorem graded_bound_saturation_holds : GradedBoundOfSaturation := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 3) * e1) (e1 + c0) κ
      (projAtOf_of highest_vector_projection p K r LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 3) * e1 + 2 * (e1 + c0) = (K + 5) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

theorem kapC_mono (p n : ℕ) {d d' : ℕ} (h : d ≤ d') : kapC p n d ≤ kapC p n d' := by
  unfold kapC
  exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))

theorem hypPE_setLast {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r) :
    ∀ o ≤ LLw.deg (Fin.last K),
      HypP p (setLast LLw o) ρ (kapC p r LLw.total) ∧ HypE p (setLast LLw o) ρ (kapC p r LLw.total) :=
  fun o ho =>
    ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho)),
      Formalism.InvariantFactorPaths.PW.Top.dischargeE p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho))⟩

theorem gram_bound_unconditional_of_sat (hR : ResSatLThm) : GramBoundUnconditional := by
  intro p hp K r hr0 LLw q J M ρ κ hr hρ hv hκ
  have hsat : ∀ e ≤ LLw.deg (Fin.last K),
      ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
        (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) := by
    intro e he
    refine resSatL_mono _ J _ ρ ?_ (hR p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
      hr hρ (by simpa [setLast] using hv))
    have ht := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    have hl : Nat.log p (4 * (setLast LLw (LLw.deg (Fin.last K) - e)).total + r - 1)
        ≤ Nat.log p (4 * LLw.total + r - 1) := Nat.log_mono_right (by omega)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hl)
  refine graded_bound_saturation_holds p K r LLw J M ρ (kapC p r LLw.total) _ κ hr hρ hv (hypPE_setLast LLw ρ) hsat ?_
  have e : (K + 5) * kapC p r LLw.total + 2 * (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1)))
      = (K + 5) * kapC p r LLw.total + 4 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1)) := by ring
  rw [e]
  exact hκ

theorem numeric_product_inequality (p a r x : ℕ) (hx : x ≤ 8 * a + r) :
    ((r.choose 2 * Nat.log p x : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgV2 p a r := by
  have hlb : 0 ≤ Real.logb p (8 * a + r) := by
    unfold Real.logb
    exact div_nonneg (by exact_mod_cast Real.log_natCast_nonneg (8 * a + r)) (Real.log_natCast_nonneg p)
  have hc : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
    have h2 : r.choose 2 * 2 ≤ r ^ 2 := by
      rw [Nat.choose_two_right]
      calc r * (r - 1) / 2 * 2 ≤ r * (r - 1) := Nat.div_mul_le_self _ _
        _ ≤ r * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = r ^ 2 := (sq r).symm
    have : ((r.choose 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ) ^ 2 := by exact_mod_cast h2
    linarith
  have hlog : ((Nat.log p x : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
    have hm : Nat.log p x ≤ Nat.log p (8 * a + r) := Nat.log_mono_right hx
    have hn : ((Nat.log p (8 * a + r) : ℕ) : ℝ) ≤ Real.logb p (8 * a + r) := by
      exact_mod_cast Real.natLog_le_logb (8 * a + r) p
    calc ((Nat.log p x : ℕ) : ℝ) ≤ ((Nat.log p (8 * a + r) : ℕ) : ℝ) := by exact_mod_cast hm
      _ ≤ _ := hn
  unfold lgV2
  rw [Nat.cast_mul]
  calc ((r.choose 2 : ℕ) : ℝ) * ((Nat.log p x : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * Real.logb p (8 * a + r) :=
        mul_le_mul hc hlog (by positivity) (by positivity)
    _ ≤ (r : ℝ) ^ 2 / 2 * (Real.logb p (8 * a + r) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem lg_nonneg (p a r : ℕ) : 0 ≤ (r : ℝ) ^ 2 * lgV2 p a r := by
  unfold lgV2
  have hlb : 0 ≤ Real.logb p (8 * a + r) := by
    unfold Real.logb
    exact div_nonneg (by exact_mod_cast Real.log_natCast_nonneg (8 * a + r)) (Real.log_natCast_nonneg p)
  exact mul_nonneg (by positivity) (by linarith)

theorem gram_bound_exponent_of_sat (hR : ResSatLThm) : GramBoundUnconditionalExponent := by
  intro p hp K r hr0 LLw q J M ρ a κ hr hρ hv htot hκ
  apply gram_bound_unconditional_of_sat hR p K r LLw J M ρ κ hr hρ hv
  have h1 := numeric_product_inequality p a r (LLw.total + r - 1) (by omega)
  have h2 := numeric_product_inequality p a r (4 * LLw.total + r - 1) (by omega)
  have h3 := lg_nonneg p a r
  unfold kapC
  generalize r.choose 2 * Nat.log p (LLw.total + r - 1) = X at h1 ⊢
  generalize r.choose 2 * Nat.log p (4 * LLw.total + r - 1) = Z at h2 ⊢
  push_cast
  have a1 : ((K : ℝ) + 5) * (X : ℝ) ≤ ((K : ℝ) + 5) * ((r : ℝ) ^ 2 / 2 * lgV2 p a r) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have a2 : 0 ≤ (K : ℝ) * ((r : ℝ) ^ 2 * lgV2 p a r) := mul_nonneg (by positivity) h3
  nlinarith [a1, a2, h2, h3, hκ]

theorem kappa_numeric_holds : KapNum := by
  intro p _ K r a d hr hd
  have h1 := numeric_product_inequality p a r (d + r - 1) (by omega)
  have hQ := lg_nonneg p a r
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hKQ := mul_nonneg hK hQ
  have h3 : ((K : ℝ) + 5) * ((kapC p r d : ℕ) : ℝ) ≤ ((K : ℝ) + 5) * ((r : ℝ) ^ 2 / 2 * lgV2 p a r) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [Nat.cast_mul]
  push_cast at h3 ⊢
  nlinarith

section Ties

variable {N : ℕ}

theorem grid_le (T : TieData) (Yl n₀ dd : Fin T.t → ℕ) (n : Fin T.t → ℕ)
    (hn : n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))) :
    ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
  intro i
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 (Fintype.mem_piFinset.1 hn i)
  rw [← hji]
  have hj' : j ≤ Yl i - 1 := by
    have := Finset.mem_range.1 hj
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _

theorem takeD_vec_last (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (n : Fin T.t → ℕ) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
  obtain ⟨h1, hv, -⟩ := hadm.2.1 i
  simp [Letters.takeD, Letters.setTies, show T.pos i < N by omega, hv]

theorem takeD_total_le (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (a : ℕ) (Yl n₀ dd : Fin T.t → ℕ)
    (hS : ∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i)
    (hdeg : ∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a)
    (n : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1)) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ 2 * a := by
  obtain ⟨hlt, -, -⟩ := hadm.2.1 i
  have htie : (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg ⟨T.pos i + 1, hlt⟩
      = n₀ i + dd i * (Yl i - 1) := by
    have hex : ∃ j, T.pos j + 1 = T.pos i + 1 := ⟨i, rfl⟩
    simp only [Letters.setTies]
    rw [dif_pos hex]
    have hc := Classical.choose_spec hex
    have hj : Classical.choose hex = i := hadm.1.injective (by omega)
    rw [hj]
  have hS2 : T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ 2 * a := by
    have h1 := hdeg ⟨T.pos i + 1, hlt⟩
    rw [htie] at h1
    have h2 := hS i
    omega
  refine le_trans ?_ hS2
  unfold Letters.total TieData.S
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : T.pos i + 1 ≤ N)) (fun _ _ _ => Nat.zero_le _))
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : j < T.pos i + 1 := Finset.mem_range.1 hj
  have hjN : j < N := by omega
  rw [dif_pos hj1, dif_pos hjN, if_pos (by simp; omega)]
  simp only [Letters.takeD, Letters.setTies, dif_pos hjN]
  split_ifs with h
  · exact hn _
  · exact le_rfl

theorem pos_num (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (p a r : ℕ) (i : Fin T.t) :
    (((T.pos i : ℕ) + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by
  obtain ⟨hlt, -⟩ := hadm.2.1 i
  have hpos : ((T.pos i : ℝ) + 3) ≤ ((N : ℝ) + 2) := by
    have : T.pos i + 3 ≤ N + 2 := by omega
    exact_mod_cast this
  have hl := lg_nonneg p a r
  have key := mul_le_mul_of_nonneg_right hpos hl
  calc (((T.pos i : ℕ) + 3) * r ^ 2 : ℝ) * lgV2 p a r = ((T.pos i : ℝ) + 3) * ((r : ℝ) ^ 2 * lgV2 p a r) := by ring
    _ ≤ ((N : ℝ) + 2) * ((r : ℝ) ^ 2 * lgV2 p a r) := key
    _ = ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by ring

end Ties

theorem theoremMFree_of (hR : ResSatLThm) : TheoremMFree := by
  obtain ⟨C₀, hC₀, hM⟩ := Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq
  have hQ : 0 ≤ ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r := by
    rw [mul_assoc]; exact mul_nonneg (by positivity) (lg_nonneg p a r)
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz (by linarith) hineq ?_
  intro n hn i
  refine gram_bound_exponent_of_sat hR p (T.pos i) r _ T.J (T.thrUpTo i) ρ a κ hr hρ (takeD_vec_last LL T hadm n i)
    (takeD_total_le LL T hadm a Yl n₀ dd hS hdeg n (grid_le T Yl n₀ dd n hn) i) ?_
  have := pos_num LL T hadm p a r i
  linarith

theorem divModP_zero {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (h0 : LL.deg (Fin.last K) = 0) : DivModP p LL J M ρ := by
  intro h hY hI a ha b hb he
  have hsupp : ∀ m ∈ h.support, m (Fin.last K, ρ) = 0 := by
    intro m hm
    have hP : h ∈ Pol p r LL := (Submodule.mem_inf.1 hY).1
    have hmd : MultiDeg LL m := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hP) hm
    have hs : ∑ c, m (Fin.last K, c) = 0 := by rw [hmd (Fin.last K), h0]
    exact (Finset.sum_eq_zero_iff.1 hs) ρ (Finset.mem_univ _)
  have hinit : initPart (Fin.last K, ρ) 0 h = h := by
    ext m
    rw [coeff_initPart]
    split_ifs with hm
    · rfl
    · symm
      by_contra hne
      exact hm (hsupp m (MvPolynomial.mem_support_iff.2 hne))
  have hXa : initPart (Fin.last K, ρ) 0 (X (Fin.last K, ρ) * a) = 0 := by
    ext m
    rw [coeff_initPart, MvPolynomial.coeff_zero]
    split_ifs with hm
    · simp [MvPolynomial.coeff_X_mul', Finsupp.mem_support_iff, hm]
    · rfl
  have hbI : initPart (Fin.last K, ρ) 0 b ∈ IntPol p (Fin (K + 1) × Fin r) := by
    obtain ⟨b0, hb0⟩ := LinearMap.mem_range.1 hb
    refine LinearMap.mem_range.2 ⟨∑ m ∈ b0.support,
      if m (Fin.last K, ρ) = 0 then monomial m (MvPolynomial.coeff m b0) else 0, ?_⟩
    rw [← hb0]
    change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (∑ m ∈ b0.support,
        if m (Fin.last K, ρ) = 0 then monomial m (MvPolynomial.coeff m b0) else 0)
      = initPart (Fin.last K, ρ) 0 (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) b0)
    unfold initPart
    rw [MvPolynomial.support_map_of_injective _ (f := algebraMap ℤ_[p] ℚ_[p]) (fun a b h => Subtype.ext h),
      map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp [MvPolynomial.map_monomial, MvPolynomial.coeff_map]
  refine ⟨0, Submodule.zero_mem _, initPart (Fin.last K, ρ) 0 b, hbI, ?_, ?_⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · rw [mul_zero, zero_add]
    calc h = initPart (Fin.last K, ρ) 0 h := hinit.symm
      _ = _ := by rw [he, initPart_add, initPart_smul, hXa, zero_add]

theorem gram_bound_mod_p_lifting_holds : GramBoundOfModPLifting := by
  intro p _ K r _ LLw q J M ρ e1 κ hr hρ hv hPE hL hκ
  refine gram_bound_of_restriction_of_proj highest_vector_projection p K r LLw J M ρ e1 κ hr hρ hv hPE ?_ hκ
  intro e he
  refine restriction_saturation_holds p K r _ J _ ρ
    (resOntoKThm_of omega_injective_holds p K r _ J _ ρ e1 hr hρ hv (hPE _ (Nat.sub_le _ _)).1) ?_
  by_cases h : e < LLw.deg (Fin.last K)
  · apply divided_power_mod_p_of p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hv
    have h1 := hL (e + 1) (by omega) h
    rw [setLast_setLast, setLast_deg_last, shiftLastLetterThresholds_add, Nat.sub_sub]
    exact h1
  · apply divModP_zero
    rw [setLast_deg_last]
    omega

theorem gram_bound_at_exponent_holds : GramBoundAtExponent := by
  intro p _ K r _ LLw q J M ρ a κ hr hρ hv ht hκ hL
  exact gram_bound_mod_p_lifting_holds p K r LLw J M ρ (kapC p r LLw.total) κ hr hρ hv (hypPE_setLast LLw ρ) hL
    ((kappa_numeric_holds p K r a LLw.total hr ht).trans hκ)

theorem lattice_bound_theorem_holds : TheoremML := by
  obtain ⟨C₀, hC₀, hM⟩ := Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq hL
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq ?_
  intro n hn i
  exact gram_bound_at_exponent_holds p (T.pos i) r _ T.J (T.thrUpTo i) ρ a κ hr hρ (takeD_vec_last LL T hadm n i)
    (takeD_total_le LL T hadm a Yl n₀ dd hS hdeg n (grid_le T Yl n₀ dd n hn) i)
    ((pos_num LL T hadm p a r i).trans hκ) (hL n hn i)

end Formalism.InvariantFactorPaths.L4
