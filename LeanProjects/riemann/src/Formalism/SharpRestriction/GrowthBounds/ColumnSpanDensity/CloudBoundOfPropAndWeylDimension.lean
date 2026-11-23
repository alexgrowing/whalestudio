import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def cloudAt {n' mm : ℕ} (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (s : Fin n') : Fin mm → ℤ :=
  fun j => lamAt lam0 s j.castSucc.succ

def dimCl {n' mm : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) : ℝ :=
  ((∏ s : TT, weylDim mm (cloudAt lam0 s.val) : ℚ) : ℝ)

def CloudLowerBoundWeyl : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) → 2 * ccl ≤ 8 * a →
    ∀ (t c₂ : ℕ) (D₁ κ₁ κ₂ : ℝ), 0 ≤ D₁ → 4 * D₁ < c₂ → 2 * TT.card * ccl ≤ c₂ → 0 ≤ κ₁ → κ₁ ≤ 1 → 0 ≤ κ₂ →
      RhoL R (flatW (mm + 1) A B) t c₂ D₁ ((1 - κ₁) * dL R (flatW (mm + 1) A B)) →
      RhoL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ D₁
        ((1 - κ₂) * dL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) →
      RhoL R lam0 t (c₂ - 2 * TT.card * ccl) (2 * D₁ + TT.card * (⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ))
        (dimCl TT lam0 * ((1 - κ₁) * dL R (flatW (mm + 1) A B) -
          κ₂ * dL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))))

theorem weylDim_add_const (n : ℕ) (lam : Fin n → ℤ) (d : ℤ) : weylDim n (fun i => lam i + d) = weylDim n lam := by
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [add_sub_add_right_eq_sub]

theorem cwt_lower (m A c B : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i ∧ μ i ≤ c) :
    (weylDim m μ : ℝ) * (weylDim (m + 2) (hwt m A B) : ℝ) ≤ (weylDim (m + 2) (cwt m A c B μ) : ℝ) := by
  rw [weylDim_cwt, weylDim_hwt]
  have hw : (0 : ℝ) ≤ weylDim m μ := by exact_mod_cast (weylDim_pos_of_antitone m μ hμ).le
  have hj : ∀ j : Fin m, (0 : ℝ) < (m : ℝ) - ((j : ℕ) : ℝ) := fun j => by
    have : ((j : ℕ) : ℝ) < m := by exact_mod_cast j.isLt
    linarith
  have hμc : ∀ j, (0 : ℝ) ≤ μ j ∧ (μ j : ℝ) ≤ c := fun j =>
    ⟨by exact_mod_cast (h0 j).1, by exact_mod_cast (h0 j).2⟩
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have h1 : (∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) ≤
      ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_le_prod (fun j _ => by positivity)
      (fun j _ => div_le_div_of_nonneg_right (by linarith [hμc j]) (by positivity))
  have h2 : (∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) ≤
      ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_le_prod (fun j _ => div_nonneg (by linarith [hj j]) (hj j).le)
      (fun j _ => div_le_div_of_nonneg_right (by linarith [hμc j]) (hj j).le)
  have h3 : ((A : ℝ) + B + m + 1) / ((m : ℝ) + 1) ≤ ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hP2 : (0 : ℝ) ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => div_nonneg (by linarith [hj j]) (hj j).le
  have hQ1 : (0 : ℝ) ≤ ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => div_nonneg (by linarith [hμc j]) (by positivity)
  have hQ2 : (0 : ℝ) ≤ ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => div_nonneg (by linarith [hj j, hμc j]) (hj j).le
  have hF : (0 : ℝ) ≤ ((A : ℝ) + B + m + 1) / ((m : ℝ) + 1) := by positivity
  have key := mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul h1 h2 hP2 hQ1) h3 hF (mul_nonneg hQ1 hQ2)) hw
  linarith

theorem top_bounds (mm P Q ccl : ℕ) (lam : Fin (mm + 2) → ℤ) (hanti : Antitone lam) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -(Q : ℤ) - ccl) (hmid : ∀ j : Fin mm, |lam j.castSucc.succ| ≤ ccl)
    (t : ℝ) (ht : 0 ≤ t) (hP : ((2 * ccl : ℕ) : ℝ) ≤ t * P) (hQ : ((2 * ccl : ℕ) : ℝ) ≤ t * Q) :
    0 < (weylDim mm (fun j => lam j.castSucc.succ) : ℝ) ∧
    (weylDim mm (fun j => lam j.castSucc.succ) : ℝ) * (weylDim (mm + 2) (hwt mm P Q) : ℝ) ≤
      (weylDim (mm + 2) lam : ℝ) ∧
    (weylDim (mm + 2) lam : ℝ) ≤ (1 + t) ^ (2 * mm + 1) *
      ((weylDim mm (fun j => lam j.castSucc.succ) : ℝ) * (weylDim (mm + 2) (hwt mm P Q) : ℝ)) := by
  set μ : Fin mm → ℤ := fun j => lam j.castSucc.succ + ccl with hμdef
  have hlam : (fun i => lam i + (ccl : ℤ)) = cwt mm P (2 * ccl) Q μ := by
    funext i
    unfold cwt
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, h0]
      push_cast
      ring
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.cons_succ, Fin.snoc_last]
        simp only [Fin.succ_last, hl]
        ring
      · simp only [Fin.cons_succ, Fin.snoc_castSucc, hμdef]
  have hw : weylDim (mm + 2) lam = weylDim (mm + 2) (cwt mm P (2 * ccl) Q μ) := by
    rw [← hlam, weylDim_add_const]
  have hm : weylDim mm (fun j => lam j.castSucc.succ) = weylDim mm μ :=
    (weylDim_add_const mm (fun j => lam j.castSucc.succ) ccl).symm
  have hμa : Antitone μ := by
    intro i j hij
    have := hanti (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mpr hij))
    simp only [hμdef]
    linarith
  have hμ0 : ∀ i, 0 ≤ μ i ∧ μ i ≤ ((2 * ccl : ℕ) : ℤ) := fun i => by
    have := abs_le.mp (hmid i)
    simp only [hμdef]
    push_cast
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    exact_mod_cast weylDim_pos_of_antitone mm μ hμa
  · rw [hm, hw]
    exact cwt_lower mm P (2 * ccl) Q μ hμa hμ0
  · rw [hm, hw]
    exact (cwt_bound mm P (2 * ccl) Q μ hμa hμ0 t ht hP hQ).2

theorem dimV_weyl (hW : WeylV) {p n' : ℕ} (R : RS p n') (mm : ℕ) (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ)
    (hdom : IsDominant lam0) :
    ((dimV R.Kf lam0 : ℕ) : ℚ) = ∏ s : Fin n', weylDim (mm + 2) (lamAt lam0 s) := by
  rw [hW R.Kf n' (mm + 1) lam0 hdom]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [weylDim, Int.cast_sub]

private theorem prod_univ_eq_prod_subtype_of_eq_one_off {n' : ℕ} (TT : Finset (Fin n')) (f : Fin n' → ℚ)
    (hf : ∀ s, s ∉ TT → f s = 1) : ∏ s : Fin n', f s = ∏ s : TT, f s.val := by
  rw [Finset.prod_coe_sort TT f]
  exact (Finset.prod_subset (Finset.subset_univ TT) (fun s _ hs => hf s hs)).symm

theorem dimV_flat (hW : WeylV) {p n' : ℕ} (R : RS p n') (mm : ℕ) {TT : Finset (Fin n')} (A B : TT → ℕ) :
    ((dimV R.Kf (flatW (mm + 1) A B) : ℕ) : ℚ) = ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℚ) := by
  rw [dimV_weyl hW R mm _ (flatW_dom mm A B)]
  rw [prod_univ_eq_prod_subtype_of_eq_one_off TT _ (fun s hs => by rw [lamAt_flat, dif_neg hs])]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [lamAt_flat, dif_pos s.2]

theorem dimV_tops (hW : WeylV) {p n' : ℕ} (R : RS p n') (mm : ℕ) (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (hdom : IsDominant lam0) (hz : ∀ s, s ∉ TT → lam0 s = 0) :
    ((dimV R.Kf lam0 : ℕ) : ℚ) = ∏ s : TT, weylDim (mm + 2) (lamAt lam0 s.val) := by
  have hone : ∀ s, s ∉ TT → weylDim (mm + 2) (lamAt lam0 s) = 1 := fun s hs => by
    have : lamAt lam0 s = fun _ => (0 : ℤ) := by
      funext i
      simp [lamAt, hz s hs, ite_apply]
    rw [this, weylDim_zero]
  rw [dimV_weyl hW R mm lam0 hdom]
  exact prod_univ_eq_prod_subtype_of_eq_one_off TT _ hone

theorem lamAt_anti {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) (s : Fin n') :
    Antitone (lamAt lam0 s) := by
  unfold lamAt
  split_ifs
  · exact hdom s
  · intro i j hij
    exact neg_le_neg (hdom s (Fin.rev_le_rev.mpr hij))

theorem top_shape {n' mm : ℕ} (TT : Finset (Fin n')) (aw bw : Fin n' → ℤ) (ccl : ℕ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (hB : IsBaseWeight TT aw bw ccl lam0) (s : Fin n') (hs : s ∈ TT) :
    lamAt lam0 s 0 = (if Even s.val then aw s else bw s) ∧
    lamAt lam0 s (Fin.last (mm + 1)) = -(if Even s.val then bw s else aw s) ∧
    ∀ j : Fin mm, |lamAt lam0 s j.castSucc.succ| ≤ ccl := by
  obtain ⟨h0, hl, hmid⟩ := (hB s).1 hs
  unfold lamAt
  split_ifs with he
  · refine ⟨h0, hl, fun j => hmid _ ?_ ?_⟩
    · simp only [Fin.val_succ, Fin.coe_castSucc]
      omega
    · have := j.isLt
      simp only [Fin.val_succ, Fin.coe_castSucc]
      omega
  · refine ⟨?_, ?_, fun j => ?_⟩
    · simp [hl]
    · simp [h0]
    · rw [abs_neg]
      have := j.isLt
      refine hmid _ ?_ ?_
      · simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
        omega
      · simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
        omega

theorem share_abs (L H Hp Cl κ₁ κ₂ ep : ℝ) (hL : 0 ≤ L) (_hH : 0 ≤ H) (hCl : 0 ≤ Cl) (h1 : 0 ≤ κ₁) (h1' : κ₁ ≤ 1)
    (h2 : 0 ≤ κ₂) (hep : 0 ≤ ep) (a1 : Cl * H ≤ L) (a2 : (1 - ep) * L ≤ Cl * H) (a3 : Hp ≤ 2 * H) :
    (1 - (κ₁ + 2 * κ₂ + ep)) * L ≤ Cl * ((1 - κ₁) * H - κ₂ * Hp) := by
  have e1 : 0 ≤ (1 - κ₁) * (Cl * H - (1 - ep) * L) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ κ₂ * (L - Cl * H) := mul_nonneg h2 (by linarith)
  have e3 : 0 ≤ κ₁ * ep * L := by positivity
  have e4 : Cl * κ₂ * Hp ≤ Cl * κ₂ * (2 * H) := mul_le_mul_of_nonneg_left a3 (mul_nonneg hCl h2)
  nlinarith [e1, e2, e3, e4]

private theorem one_sub_mul_exp_le_one_of_le (x ep : ℝ) (hx : x ≤ ep) : (1 - ep) * Real.exp x ≤ 1 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos x
  nlinarith [mul_le_mul_of_nonneg_right h1 h3.le, mul_le_mul_of_nonneg_right hx h3.le]

private theorem one_add_pow_le_exp_mul (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ Real.exp (N * t) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) N

private theorem top_facts_lemma_4 {n' mm : ℕ} (TT : Finset (Fin n')) (aw bw : Fin n' → ℤ) (ccl : ℕ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ) (hB : IsBaseWeight TT aw bw ccl lam0)
    (hdom : IsDominant lam0) (hAB : ∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl)
    (t0 : ℝ) (ht0 : 0 ≤ t0)
    (hPA : ∀ s : TT, ((2 * ccl : ℕ) : ℝ) ≤ t0 * A s ∧ ((2 * ccl : ℕ) : ℝ) ≤ t0 * B s) (s : TT) :
    0 < (weylDim mm (cloudAt lam0 s.val) : ℝ) ∧
    (weylDim mm (cloudAt lam0 s.val) : ℝ) * (dimHar (mm + 1) (A s) (B s) : ℝ) ≤
      (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ) ∧
    (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ) ≤
      (1 + t0) ^ (2 * mm + 1) * ((weylDim mm (cloudAt lam0 s.val) : ℝ) * (dimHar (mm + 1) (A s) (B s) : ℝ)) := by
  obtain ⟨e0, el, emid⟩ := top_shape TT aw bw ccl lam0 hB s.val s.2
  obtain ⟨hA, hB'⟩ := hAB s
  have hanti := lamAt_anti lam0 hdom s.val
  split_ifs at e0 el with he
  · have h := top_bounds mm (A s) (B s) ccl (lamAt lam0 s.val) hanti (by rw [e0]; linarith)
      (by rw [el]; linarith) emid t0 ht0 (hPA s).1 (hPA s).2
    rw [weylDim_hwt_eq] at h
    push_cast at h
    exact h
  · have h := top_bounds mm (B s) (A s) ccl (lamAt lam0 s.val) hanti (by rw [e0]; linarith)
      (by rw [el]; linarith) emid t0 ht0 (hPA s).2 (hPA s).1
    rw [weylDim_hwt_eq, dimHar_comm] at h
    push_cast at h
    exact h

theorem cloud_bound_of_prop_and_weyl_dimension (hP : CloudLowerBoundWeyl) (hW : WeylV) : CloudWeightLowerBound := by
  intro p n' R m hm TT a ccl b' aw bw lam0 A B hB hdom hz hAB hb' hbA ha hsmall t c₂ D₁ κ₁ κ₂ hD hc hc2
    hk1 hk1' hk2 h1 h2
  obtain ⟨mm, rfl⟩ : ∃ mm, m = mm + 1 := ⟨m - 1, by omega⟩
  have key := hP p n' R mm (by omega) TT a ccl aw bw lam0 A B hB hdom hz hAB ha t c₂ D₁ κ₁ κ₂ hD hc hc2
    hk1 hk1' hk2 h1 h2
  refine RhoL_mono (ht := le_rfl) (hD := le_rfl) (hX := ?_) (h := key)
  set ep : ℝ := 12 * (TT.card : ℝ) * (((mm + 1 : ℕ) : ℝ) + 1) * ccl / b' with hepdef
  set t0 : ℝ := 6 * ccl / b' with ht0def
  have ht0 : 0 ≤ t0 := by positivity
  have hep0 : 0 ≤ ep := by positivity
  have hPA : ∀ s : TT, ((2 * ccl : ℕ) : ℝ) ≤ t0 * A s ∧ ((2 * ccl : ℕ) : ℝ) ≤ t0 * B s := by
    intro s
    obtain ⟨hA3, hB3⟩ := hbA s
    have e : t0 * (b' / 3) = 2 * ccl := by
      rw [ht0def]
      field_simp
      ring
    push_cast
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hA3 ht0, mul_le_mul_of_nonneg_left hB3 ht0]
  have hF := top_facts_lemma_4 TT aw bw ccl lam0 A B hB hdom hAB t0 ht0 hPA
  have hG : ∀ s : TT, (dimHar (mm + 1) (A s + 2 * ccl) (B s + 2 * ccl) : ℝ) ≤
      (1 + t0) ^ (2 * mm + 1) * (dimHar (mm + 1) (A s) (B s) : ℝ) := fun s => by
    have h := hwt_bound mm (A s) (2 * ccl) (B s) t0 ht0 (hPA s).1 (hPA s).2
    rw [weylDim_hwt_eq, weylDim_hwt_eq] at h
    push_cast at h ⊢
    exact h
  have hN := gaussianNumber_prime_pow_pos R (mm + 1 + 1) (by omega)
  have hVL : (dimV R.Kf lam0 : ℝ) = ∏ s : TT, (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (dimV_tops hW R mm TT lam0 hdom hz)
    push_cast at this
    exact this
  have hVf : (dimV R.Kf (flatW (mm + 1) A B) : ℝ) = ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (dimV_flat hW R mm A B)
    push_cast at this
    exact this
  have hVf2 : (dimV R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) : ℝ) =
      ∏ s : TT, (dimHar (mm + 1) (A s + 2 * ccl) (B s + 2 * ccl) : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (dimV_flat hW R mm (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))
    push_cast at this
    exact this
  have hCl : dimCl TT lam0 = ∏ s : TT, (weylDim mm (cloudAt lam0 s.val) : ℝ) := by
    unfold dimCl
    push_cast
    rfl
  set E : ℝ := (1 + t0) ^ ((2 * mm + 1) * TT.card) with hEdef
  have hc0 : ∀ s : TT, 0 ≤ (weylDim mm (cloudAt lam0 s.val) : ℝ) * (dimHar (mm + 1) (A s) (B s) : ℝ) :=
    fun s => mul_nonneg (hF s).1.le (Nat.cast_nonneg _)
  have P1 : (∏ s : TT, (weylDim mm (cloudAt lam0 s.val) : ℝ)) * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) ≤
      ∏ s : TT, (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun s _ => hc0 s) (fun s _ => (hF s).2.1)
  have P2 : ∏ s : TT, (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ) ≤
      E * ((∏ s : TT, (weylDim mm (cloudAt lam0 s.val) : ℝ)) * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ)) := by
    calc ∏ s : TT, (weylDim (mm + 2) (lamAt lam0 s.val) : ℝ)
        ≤ ∏ s : TT, ((1 + t0) ^ (2 * mm + 1) *
            ((weylDim mm (cloudAt lam0 s.val) : ℝ) * (dimHar (mm + 1) (A s) (B s) : ℝ))) :=
          Finset.prod_le_prod (fun s _ => (hc0 s).trans (hF s).2.1) (fun s _ => (hF s).2.2)
      _ = E * ((∏ s : TT, (weylDim mm (cloudAt lam0 s.val) : ℝ)) * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_coe, ← pow_mul]
  have P3 : ∏ s : TT, (dimHar (mm + 1) (A s + 2 * ccl) (B s + 2 * ccl) : ℝ) ≤
      E * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) := by
    calc ∏ s : TT, (dimHar (mm + 1) (A s + 2 * ccl) (B s + 2 * ccl) : ℝ)
        ≤ ∏ s : TT, ((1 + t0) ^ (2 * mm + 1) * (dimHar (mm + 1) (A s) (B s) : ℝ)) :=
          Finset.prod_le_prod (fun s _ => Nat.cast_nonneg _) (fun s _ => hG s)
      _ = E * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
  have hx : (((2 * mm + 1) * TT.card : ℕ) : ℝ) * t0 ≤ ep := by
    rw [hepdef, ht0def]
    push_cast
    have hcd : (0 : ℝ) ≤ (TT.card : ℝ) * ccl := by positivity
    have e1 : ((2 * (mm : ℝ) + 1) * TT.card) * (6 * ccl / b') = (6 * (2 * (mm : ℝ) + 1) * (TT.card * ccl)) / b' := by
      ring
    have e2 : 12 * (TT.card : ℝ) * ((mm : ℝ) + 1 + 1) * ccl / b' = (12 * ((mm : ℝ) + 2) * (TT.card * ccl)) / b' := by
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by nlinarith) hb'.le
  have hEx := one_add_pow_le_exp_mul t0 ht0 ((2 * mm + 1) * TT.card)
  have hE1 : (1 - ep) * E ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hEx (by linarith)) (one_sub_mul_exp_le_one_of_le _ ep hx)
  have hE2 : E ≤ 2 := by
    have := one_sub_mul_exp_le_one_of_le _ (1 / 9) (hx.trans hsmall)
    nlinarith
  have hClnn : 0 ≤ dimCl TT lam0 := by
    rw [hCl]
    exact Finset.prod_nonneg fun s _ => (hF s).1.le
  have hVfnn : (0 : ℝ) ≤ ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) :=
    Finset.prod_nonneg fun s _ => Nat.cast_nonneg _
  have hCV : 0 ≤ (∏ s : TT, (weylDim mm (cloudAt lam0 s.val) : ℝ)) * ∏ s : TT, (dimHar (mm + 1) (A s) (B s) : ℝ) :=
    mul_nonneg (hCl ▸ hClnn) hVfnn
  have a1 : dimCl TT lam0 * dL R (flatW (mm + 1) A B) ≤ dL R lam0 := by
    unfold dL
    rw [hCl, hVL, hVf, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right P1 hN.le
  have a2 : (1 - ep) * dL R lam0 ≤ dimCl TT lam0 * dL R (flatW (mm + 1) A B) := by
    unfold dL
    rw [hCl, hVL, hVf, ← mul_div_assoc, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hN.le
    have h1e : 0 ≤ 1 - ep := by linarith
    nlinarith [mul_le_mul_of_nonneg_left P2 h1e, mul_le_mul_of_nonneg_right hE1 hCV]
  have a3 : dL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) ≤
      2 * dL R (flatW (mm + 1) A B) := by
    unfold dL
    rw [hVf2, hVf, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hN.le
    nlinarith [mul_le_mul_of_nonneg_right hE2 hVfnn]
  exact share_abs _ _ _ _ _ _ _ (dL_nonneg R lam0) (dL_nonneg R _) hClnn hk1 hk1' hk2 hep0 a1 a2 a3

end Formalism.MainNotions.flipOneThree.Pf

end
