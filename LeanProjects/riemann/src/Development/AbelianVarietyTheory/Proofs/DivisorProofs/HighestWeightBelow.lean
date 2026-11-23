import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Weights

open Finset

theorem highestWeight_below {a b t : ℕ} (hb : b = a + t) {E F : Finset ℚ} (c : ℚ) (hE : E.card = a)
    (hFe : F = E ∪ TPar.block c t) (hlt : ∀ x ∈ E, ∀ y ∈ TPar.block c t, y < x) (hF : F.card = b) :
    (∀ r : Fin a, highestWeight F hF (Fin.castLE (by omega) r) = highestWeight E hE r - (t : ℚ) / 2) ∧
      ∀ r : Fin b, a ≤ r.1 → highestWeight F hF r = c + (a : ℚ) / 2 := by
  subst hb hFe
  let g : Fin (a + t) → ℚ := fun i =>
    if h : i.1 < a then descEnum E hE ⟨i.1, h⟩ else c + ((t : ℚ) - 1) / 2 - ((i.1 - a : ℕ) : ℚ)
  have hblock : ∀ i : Fin (a + t), ¬ i.1 < a → g i ∈ TPar.block c t := fun i h => by
    simp only [g, dif_neg h]
    exact mem_block.2 ⟨i.1 - a, by omega, rfl⟩
  have hmem : ∀ i : Fin (a + t), i.1 < a → g i ∈ E := fun i h => by
    simp only [g, dif_pos h]
    exact descEnum_mem _ _ _
  have hg : StrictAnti g := by
    intro i j hij
    have hij' : i.1 < j.1 := hij
    by_cases hi : i.1 < a
    · by_cases hj : j.1 < a
      · simp only [g, dif_pos hi, dif_pos hj]
        exact strictAnti_descEnum E hE (by simpa using hij')
      · exact hlt _ (hmem i hi) _ (hblock j hj)
    · have hj : ¬ j.1 < a := by omega
      simp only [g, dif_neg hi, dif_neg hj]
      have : ((i.1 - a : ℕ) : ℚ) < ((j.1 - a : ℕ) : ℚ) := by exact_mod_cast (by omega : i.1 - a < j.1 - a)
      linarith
  have key := descEnum_unique hF hg fun i => by
    by_cases h : i.1 < a
    · exact mem_union_left _ (hmem i h)
    · exact mem_union_right _ (hblock i h)
  refine ⟨fun r => ?_, fun r hr => ?_⟩
  · have h : (Fin.castLE (by omega) r : Fin (a + t)).1 < a := r.2
    simp only [highestWeight, key, g, dif_pos h]
    push_cast
    simp only [Fin.val_castLE, Fin.eta]
    ring
  · have h : ¬ r.1 < a := by omega
    simp only [highestWeight, key, g, dif_neg h]
    rw [Nat.cast_sub hr]
    push_cast
    ring

theorem highestWeight_add {n : ℕ} {E : Finset ℚ} (δ : ℚ) (hE : E.card = n) (h : (E.image (· + δ)).card = n) (r : Fin n) :
    highestWeight (E.image (· + δ)) h r = highestWeight E hE r + δ := by
  have key := descEnum_unique (f := fun i => descEnum E hE i + δ) h
    (fun i j hij => by simpa using strictAnti_descEnum E hE hij) fun i => mem_image_of_mem _ (descEnum_mem E hE i)
  simp only [highestWeight, key]
  ring

theorem highestWeight_neg {n : ℕ} {E : Finset ℚ} (hE : E.card = n) (h : (E.image Neg.neg).card = n) (r : Fin n) :
    highestWeight (E.image Neg.neg) h r = -highestWeight E hE r.rev := by
  have key := descEnum_unique (f := fun i => -descEnum E hE i.rev) h
    (fun i j hij => by simpa using strictAnti_descEnum E hE (Fin.rev_lt_rev.2 hij))
    fun i => mem_image_of_mem _ (descEnum_mem E hE _)
  have hr : ((r.rev : ℕ) : ℚ) = (n : ℚ) - 1 - (r : ℕ) := by
    have h1 : (r.rev : ℕ) + (r : ℕ) + 1 = n := by have := r.2; simp only [Fin.val_rev]; omega
    have h2 : ((r.rev : ℕ) : ℚ) + (r : ℕ) + 1 = n := by exact_mod_cast h1
    linarith
  simp only [highestWeight, key, hr]
  ring

theorem natW_step {a b t : ℕ} (hb : b = a + t) (ha : 0 < a) {E F : Finset ℚ} (δ c : ℚ) (hE : E.card = a)
    (hFe : F = E.image (· + δ) ∪ TPar.block c t) (hlt : ∀ x ∈ E, ∀ y ∈ TPar.block c t, y < x + δ) (hF : F.card = b)
    (lam : DomWeight a) (lam' : DomWeight b) (h1 : ∀ r, (lam.w r : ℚ) = highestWeight E hE r)
    (h2 : ∀ r, (lam'.w r : ℚ) = highestWeight F hF r) (r : Fin b) :
    lam'.natW r = if h : r.1 < a then lam.natW ⟨r.1, h⟩ + lam'.natW ⟨a - 1, by omega⟩ else 0 := by
  have hE' : (E.image (· + δ)).card = a := by
    rw [card_image_of_injective _ (add_left_injective δ), hE]
  obtain ⟨w1, w2⟩ := highestWeight_below hb c hE' hFe (fun x hx y hy => by
    obtain ⟨x, hx', rfl⟩ := mem_image.1 hx
    exact hlt x hx' y hy) hF
  have hdiff : ∀ r s : Fin a, lam'.w (Fin.castLE (by omega) r) - lam'.w (Fin.castLE (by omega) s) = lam.w r - lam.w s := by
    intro r s
    have : ((lam'.w (Fin.castLE (by omega) r) - lam'.w (Fin.castLE (by omega) s) : ℤ) : ℚ) = ((lam.w r - lam.w s : ℤ) : ℚ) := by
      push_cast
      rw [h2, h2, h1, h1, w1, w1, highestWeight_add δ hE hE', highestWeight_add δ hE hE']
      ring
    exact_mod_cast this
  have hb0 : 0 < b := by omega
  have hS : lam'.detShift = lam'.w ⟨b - 1, by omega⟩ := by rw [DomWeight.detShift, dif_pos hb0]
  have hS0 : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by rw [DomWeight.detShift, dif_pos ha]
  by_cases h : r.1 < a
  · rw [dif_pos h]
    simp only [DomWeight.natW]
    have e1 := hdiff ⟨r.1, h⟩ ⟨a - 1, by omega⟩
    have e2 : (Fin.castLE (by omega) (⟨r.1, h⟩ : Fin a) : Fin b) = r := Fin.ext rfl
    have e3 : (Fin.castLE (by omega) (⟨a - 1, by omega⟩ : Fin a) : Fin b) = ⟨a - 1, by omega⟩ := Fin.ext rfl
    rw [e2, e3] at e1
    have a1 : lam.w ⟨a - 1, by omega⟩ ≤ lam.w ⟨r.1, h⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 : lam'.w ⟨b - 1, by omega⟩ ≤ lam'.w ⟨a - 1, by omega⟩ := lam'.anti (Fin.mk_le_mk.2 (by omega))
    rw [hS, hS0]
    omega
  · rw [dif_neg h]
    have e : (lam'.w r : ℚ) = lam'.w ⟨b - 1, by omega⟩ := by
      rw [h2, h2, w2 r (by omega), w2 _ (by simp only; omega)]
    have e' : lam'.w r = lam'.w ⟨b - 1, by omega⟩ := by exact_mod_cast e
    simp [DomWeight.natW, hS, e']

end Weights

section Num

open Finset

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem num_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩

theorem num_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩

theorem num_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  exact GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩

theorem num_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
  rw [num_e D C τ h1 h2, num_b D C τ h1 h2]
  exact (D.hc τ).gap_be _

theorem num_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
  rw [num_e D C τ h1 (by omega), num_b D C τ (by omega) h2]
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))

theorem num_b_le {i j : ℕ} (h1 : 1 ≤ i) (h : i ≤ j) (h2 : j ≤ D.R.m) : ((Γ).b i : ℚ) ≤ (Γ).b j := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact_mod_cast ((Γ).b_mono i j h1 h h2).le

theorem num_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
  induction l', h using Nat.le_induction with
  | base =>
    linarith [num_be D C τ (l := l + 1) (by omega) h2, num_eb D C τ h1 h2]
  | succ n hn ih =>
    have := ih (by omega)
    have e1 := num_be D C τ (l := n + 1) (by omega) h2
    have e2 := num_eb D C τ (l := n) (by omega) h2
    have : (0 : ℚ) ≤ D.R.t := by positivity
    linarith

theorem num_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hk : 2 ≤ D.R.k := by omega
  have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
    rw [num_v D C τ hk le_rfl, num_b D C τ le_rfl hm]
    have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [e3] at e2
    exact e1.trans e2
  have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
  have step : (Γ).v D.R.k ≤ (Γ).v i := by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
  have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
  exact_mod_cast this

theorem num_ga : sLen D + 2 ≤ gap D C := by
  have := (isLeast_gap D C).1.2.1
  omega

theorem blockM_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockM l) :
    -((Γ).e l : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + ((D.R.t : ℚ) - 1) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block h)
  have e : ((Γ).t : ℚ) = D.R.t := rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

theorem blockMPlus_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockMPlus l) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block h)
  have e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

theorem blockC_bd {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ (Γ).blockC i) :
    (Γ).a i < x ∧ x < (Γ).a i + (Γ).ga := by
  have e1 := abs_le.1 (abs_sub_le_of_mem_block hx)
  have e2 := abs_le.1 (num_nearMid D C τ i (mem_Icc.2 ⟨h1, h2⟩))
  rw [(Γ).mid_eq h1] at e2
  have e3 : ((Γ).s : ℚ) + 2 ≤ (Γ).ga := by exact_mod_cast num_ga D C
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

theorem a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ (Γ).ga := by positivity
    linarith [a_add_le (G := Γ) h]

theorem v_le_two {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : ((Γ).v i : ℚ) ≤ (Γ).v 2 := by
  rcases h1.eq_or_lt with rfl | h
  · exact le_rfl
  · exact_mod_cast ((Γ).v_anti 2 i le_rfl h h2).le

theorem v_lt_a {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : ((Γ).v i : ℚ) < (Γ).a (Γ).m := by
  have : (0 : ℚ) ≤ (Γ).ga := by positivity
  rw [(Γ).a_m]
  linarith [v_le_two D C τ h1 h2]

theorem weightX_above {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (Γ).weightX j) (hy : y ∈ (Γ).blockMPlus (j + 1)) : y < x := by
  have hm : 1 ≤ D.R.m := by omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hg : (0 : ℚ) ≤ (Γ).ga := by positivity
  obtain ⟨y1, y2⟩ := blockMPlus_bd D C τ hy
  have hbe := num_be D C τ (l := 1) le_rfl hm
  have he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact le_rfl
    · linarith [num_e_lt D C τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]
  have hlow : y < -((Γ).b 1 : ℚ) := by linarith
  have hc2 := num_cloud D C τ (i := 2) le_rfl hk
  have ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2 := (Γ).a_m
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    linarith [a_le D C τ hi]
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have := num_cloud D C τ h1 h2
    simp only [GridData.vHalf]
    linarith
  · have := (blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 h).1
    linarith [a_le D C τ h2]
  · have := num_e_lt D C τ h1 (by omega : l < j + 1) hj
    have := (blockMPlus_bd D C τ h).1
    linarith

theorem card_weightX {j : ℕ} (hj : j ≤ D.R.m) : ((Γ).weightX j).card = rankX D j := by
  induction j with
  | zero =>
    rw [card_weightX_zero (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C)]
    simp [rankX]; rfl
  | succ j ih =>
    rw [(Γ).weightX_succ, card_union_of_disjoint
      (disjoint_left.2 fun x hx hy => (weightX_above D C τ hj hx hy).ne rfl), ih (by omega)]
    have : ((Γ).blockMPlus (j + 1)).card = D.R.t + 1 := card_block _ _
    rw [this]
    simp only [rankX]
    ring

theorem inCoset_weightX {j : ℕ} : InCoset (1 / 2) ((Γ).weightX j) := by
  induction j with
  | zero => exact inCoset_weightX_zero (odd_sLen D)
  | succ j ih =>
    rw [(Γ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((Γ).t : ℚ) = 2 * u + 1 := by
        have : ((Γ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(Γ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem rankX_even (j : ℕ) : Even (rankX D j) := even_rankX D j

theorem isHC_top {j n : ℕ} (hj : j ≤ D.R.m) (hn : n = rankX D j) : IsHC n (Node.par D C (.top j) τ) := by
  have he : entries (Node.par D C (.top j) τ) = (Γ).weightX j := entries_plus _
  have hr : IsRegular (Node.par D C (.top j) τ) := isRegular_plus _
  refine ⟨hr, ?_, ?_⟩
  · rw [← hr.card_entries, he, card_weightX D C τ hj, hn]
  · rw [he]
    intro x hx
    obtain ⟨y, rfl⟩ := inCoset_weightX D C τ x hx
    obtain ⟨u, hu⟩ := rankX_even D j
    refine ⟨y + 1 - u, ?_⟩
    rw [hn, hu]; push_cast; ring

end Num

section Grid

open Finset

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem entries_shift (h : ℚ) (S : SPar) : entries (shift h S) = (entries S).image (· + h) := by
  simp only [GlobalTheory.SignedHC.entries, shift, image_image]
  rfl

theorem isRegular_shift {h : ℚ} {S : SPar} (hS : IsRegular S) : IsRegular (shift h S) := by
  intro x hx y hy e
  exact hS (x.1 - h, x.2) (mem_shift.1 hx) (y.1 - h, y.2) (mem_shift.1 hy) (by simp only [e])

theorem card_shift (h : ℚ) (S : SPar) : (shift h S).card = S.card :=
  card_image_of_injective _ fun x y e => by
    simp only [Prod.mk.injEq] at e
    exact Prod.ext (add_right_cancel e.1) e.2

theorem card_cloud : (Γ).cloud.card = D.R.k - 1 := by
  rw [GridData.cloud, card_image_of_injOn, Nat.card_Icc]
  · rfl
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : (Γ).v i = (Γ).v j := by
      have : ((Γ).v i : ℚ) = (Γ).v j := h
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e ((Γ).v_anti i j hi.1 h' hj.2).ne'
    · exact h'
    · exact absurd e ((Γ).v_anti j i hj.1 h' hi.2).ne

theorem card_lows : (Γ).lows.card = D.R.m := by
  rw [GridData.lows, card_image_of_injOn, Nat.card_Icc]
  · rfl
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : (Γ).b i = (Γ).b j := by
      have : ((Γ).b i : ℚ) = (Γ).b j := by simpa using h
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e ((Γ).b_mono i j hi.1 h' hj.2).ne
    · exact h'
    · exact absurd e ((Γ).b_mono j i hj.1 h' hi.2).ne'

theorem card_Ms : ((Icc 1 (Γ).m).biUnion (Γ).blockM).card = D.R.m * D.R.t := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc 1 (Γ).m, ((Γ).blockM u).card = D.R.t := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    rfl
  · intro i hi j hj hij
    have hi := mem_Icc.1 hi
    have hj := mem_Icc.1 hj
    have ht : (0 : ℚ) ≤ D.R.t := by positivity
    refine disjoint_left.2 fun x h1 h2 => ?_
    obtain ⟨a1, a2⟩ := blockM_bd D C τ h1
    obtain ⟨b1, b2⟩ := blockM_bd D C τ h2
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [num_e_lt D C τ hi.1 h hj.2]
    · linarith [num_e_lt D C τ hj.1 h hi.2]

theorem card_Cs {i : ℕ} (hi : i ≤ D.R.m) : ((Icc ((Γ).m - i + 1) (Γ).m).biUnion (Γ).blockC).card = i * sLen D := by
  have hm : (Γ).m = D.R.m := rfl
  rw [card_biUnion]
  · have : ∀ u ∈ Icc ((Γ).m - i + 1) (Γ).m, ((Γ).blockC u).card = sLen D := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul, hm]
    congr 1
    omega
  · intro u hu v hv huv
    have hu := mem_Icc.1 hu
    have hv := mem_Icc.1 hv
    refine disjoint_left.2 fun x h1 h2 => ?_
    have b1 := blockC_bd D C τ (by omega) hu.2 h1
    have b2 := blockC_bd D C τ (by omega) hv.2 h2
    rcases lt_or_gt_of_ne huv with h | h <;> linarith [a_add_le (G := Γ) h, b1.1, b1.2, b2.1, b2.2]

theorem lows_le {x : ℚ} (hx : x ∈ (Γ).lows) : x ≤ -((Γ).b 1 : ℚ) := by
  obtain ⟨l, h1, h2, rfl⟩ := GridData.mem_lows.1 hx
  linarith [num_b_le D C τ le_rfl h1 h2]

theorem Ms_lt {x : ℚ} (hx : x ∈ (Icc 1 (Γ).m).biUnion (Γ).blockM) : x < -((Γ).b 1 : ℚ) := by
  obtain ⟨l, hl, hx⟩ := mem_biUnion.1 hx
  have hl := mem_Icc.1 hl
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hbe := num_be D C τ hl.1 hl.2
  have hb := num_b_le D C τ le_rfl hl.1 hl.2
  linarith [(blockM_bd D C τ hx).2]

theorem cloud_gt {x : ℚ} (hx : x ∈ (Γ).cloud) : -((Γ).b 1 : ℚ) < x ∧ x < (Γ).a (Γ).m := by
  obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloud.1 hx
  exact ⟨by linarith [num_cloud D C τ h1 h2], v_lt_a D C τ h1 h2⟩

theorem low_lt_a {x : ℚ} (h : x ≤ -((Γ).b 1 : ℚ)) : x < (Γ).a (Γ).m := by
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  linarith [cloud_gt D C τ (x := ((Γ).v 2 : ℚ)) (GridData.mem_cloud.2 ⟨2, le_rfl, hk, rfl⟩)]

theorem disj_lows_Ms : Disjoint (Γ).lows ((Icc 1 (Γ).m).biUnion (Γ).blockM) := by
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hm : (Γ).m = D.R.m := rfl
  refine disjoint_left.2 fun x h0 h2 => ?_
  obtain ⟨l, h1, h1', rfl⟩ := GridData.mem_lows.1 h0
  obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
  have hu := mem_Icc.1 hu
  obtain ⟨c1, c2⟩ := blockM_bd D C τ h2
  rcases le_or_gt l u with h | h
  · linarith [num_be D C τ hu.1 hu.2, num_b_le D C τ h1 h hu.2]
  · linarith [num_eb D C τ (l := u) hu.1 (by omega), num_b_le D C τ (i := u + 1) (j := l) (by omega) (by omega) (by omega)]

theorem card_entries_parD {i : ℕ} (hi : i ≤ D.R.m) : (entries ((Γ).parD i (Γ).m)).card = rankV D i D.R.m := by
  have d1 : Disjoint (Γ).cloud (Γ).lows := disjoint_left.2 fun x h1 h2 => by
    linarith [(cloud_gt D C τ h1).1, lows_le D C τ h2]
  have d2 : Disjoint ((Γ).cloud ∪ (Γ).lows) ((Icc 1 (Γ).m).biUnion (Γ).blockM) := by
    refine disjoint_union_left.2 ⟨disjoint_left.2 fun x h1 h2 => ?_, disj_lows_Ms D C τ⟩
    linarith [(cloud_gt D C τ h1).1, Ms_lt D C τ h2]
  have d3 : Disjoint ((Γ).cloud ∪ (Γ).lows ∪ (Icc 1 (Γ).m).biUnion (Γ).blockM)
      ((Icc ((Γ).m - i + 1) (Γ).m).biUnion (Γ).blockC) := by
    refine disjoint_left.2 fun x h1 h2 => ?_
    obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
    have hu := mem_Icc.1 hu
    have hb := (blockC_bd D C τ (by omega) hu.2 h2).1
    have ha := a_le D C τ hu.2
    have : x < (Γ).a (Γ).m := by
      rcases mem_union.1 h1 with h1 | h1
      · rcases mem_union.1 h1 with h1 | h1
        · exact (cloud_gt D C τ h1).2
        · exact low_lt_a D C τ (lows_le D C τ h1)
      · exact low_lt_a D C τ (Ms_lt D C τ h1).le
    linarith
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [GridData.entries_parD, card_union_of_disjoint d3, card_union_of_disjoint d2, card_union_of_disjoint d1,
    card_cloud, card_lows, card_Ms, card_Cs D C τ hi]
  simp only [rankV, Ranks.r]
  omega

theorem card_parD {i : ℕ} (hi : i ≤ D.R.m) : ((Γ).parD i (Γ).m).card = rankV D i D.R.m := by
  refine le_antisymm ?_ ((card_entries_parD D C τ hi).symm.le.trans card_image_le)
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have e : rankV D i D.R.m = (D.R.k - 1) + D.R.m + D.R.m * D.R.t + i * sLen D := by
    simp only [rankV, Ranks.r]
    omega
  rw [e, GridData.parD]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)) ?_)
  · exact card_image_le.trans (card_cloud D C τ).le
  · refine card_image_le.trans ?_
    rw [Nat.card_Icc]
    show D.R.m + 1 - 1 ≤ D.R.m
    omega
  · exact card_image_le.trans (card_Ms D C τ).le
  · exact card_image_le.trans (card_Cs D C τ hi).le

theorem isRegular_parD {i : ℕ} (hi : i ≤ D.R.m) : IsRegular ((Γ).parD i (Γ).m) :=
  isRegular_iff_card.2 ((card_entries_parD D C τ hi).trans (card_parD D C τ hi).symm)

theorem entries_parD_int {i j : ℕ} {x : ℚ} (hx : x ∈ entries ((Γ).parD i j)) : ∃ z : ℤ, x = z := by
  have hb : ∀ (c : ℤ) (n : ℕ) (y : ℚ), Odd n → y ∈ TPar.block (c : ℚ) n → ∃ z : ℤ, y = z := by
    intro c n y hn hy
    obtain ⟨a, -, rfl⟩ := mem_block.1 hy
    obtain ⟨u, rfl⟩ := hn
    exact ⟨c + u - a, by push_cast; ring⟩
  rw [GridData.entries_parD] at hx
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · rcases mem_union.1 hx with hx | hx
      · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloud.1 hx
        exact ⟨_, rfl⟩
      · obtain ⟨i, -, -, rfl⟩ := GridData.mem_lows.1 hx
        exact ⟨-(Γ).b i, by push_cast; rfl⟩
    · obtain ⟨u, -, hx⟩ := mem_biUnion.1 hx
      have hx' : x ∈ TPar.block ((-(Γ).e u : ℤ) : ℚ) D.R.t := by
        rw [Int.cast_neg]
        exact hx
      exact hb _ _ _ D.R.t_odd hx'
  · obtain ⟨u, -, hx⟩ := mem_biUnion.1 hx
    exact hb _ _ _ (odd_sLen D) hx

theorem isHC_grid {i n : ℕ} (hi : i ≤ D.R.m) (hn : n = rankV D i D.R.m) : IsHC n (Node.par D C (.grid i D.R.m) τ) := by
  refine ⟨isRegular_shift (isRegular_parD D C τ hi), ?_, ?_⟩
  · exact (card_shift _ _).trans ((card_parD D C τ hi).trans hn.symm)
  · intro x hx
    have hx' : x ∈ entries (shift (if Odd (i + D.R.m) then -(1 / 2) else 0) ((Γ).parD i (Γ).m)) := hx
    rw [entries_shift] at hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
    obtain ⟨z, rfl⟩ := entries_parD_int D C τ hy
    by_cases ho : Odd (i + D.R.m)
    · obtain ⟨u, hu⟩ := (even_rankV D i D.R.m).2 ho
      refine ⟨z + 1 - (u : ℤ) - 1 + 1 - 1, ?_⟩
      rw [if_pos ho, hn, hu]
      push_cast
      ring
    · have ho' : Odd (rankV D i D.R.m) := Nat.not_even_iff_odd.1 fun h => ho ((even_rankV D i D.R.m).1 h)
      obtain ⟨u, hu⟩ := ho'
      refine ⟨z - u, ?_⟩
      rw [if_neg ho, hn, hu]
      push_cast
      ring

theorem entries_parD_succ {i j : ℕ} (hi : i + 1 ≤ D.R.m) :
    entries ((Γ).parD (i + 1) j) = entries ((Γ).parD i j) ∪ (Γ).blockC ((Γ).m - i) := by
  have hm : (Γ).m = D.R.m := rfl
  have e : Icc ((Γ).m - (i + 1) + 1) (Γ).m = insert ((Γ).m - i) (Icc ((Γ).m - i + 1) (Γ).m) := by
    ext l
    simp only [mem_insert, mem_Icc]
    omega
  rw [GridData.entries_parD, GridData.entries_parD, e, biUnion_insert, union_comm ((Γ).blockC _)]
  simp only [union_assoc]

theorem parD_below {i : ℕ} (hi : i + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ entries ((Γ).parD i (Γ).m)) (hy : y ∈ (Γ).blockC ((Γ).m - i)) :
    x < y := by
  have hm : (Γ).m = D.R.m := rfl
  have hb := (blockC_bd D C τ (by omega) (by omega) hy).1
  have ha := a_le D C τ (i := (Γ).m - i) (j := (Γ).m) (by omega)
  rw [GridData.entries_parD] at hx
  rcases mem_union.1 hx with hx | hx
  · have : x < (Γ).a (Γ).m := by
      rcases mem_union.1 hx with hx | hx
      · rcases mem_union.1 hx with hx | hx
        · exact (cloud_gt D C τ hx).2
        · exact low_lt_a D C τ (lows_le D C τ hx)
      · exact low_lt_a D C τ (Ms_lt D C τ hx).le
    linarith
  · obtain ⟨u, hu, hx⟩ := mem_biUnion.1 hx
    have hu := mem_Icc.1 hu
    have b := (blockC_bd D C τ (by omega) (by omega) hx).2
    have := a_add_le (G := Γ) (i := (Γ).m - i) (j := u) (by omega)
    linarith

end Grid

section Final

open Finset

theorem neg_sub_mem_block {c h x : ℚ} {t : ℕ} : -x - h ∈ TPar.block (-c - h) t ↔ x ∈ TPar.block c t := by
  rw [sub_eq_add_neg (-c) h, ← sub_mem_block, sub_neg_eq_add, sub_add_cancel]
  exact neg_mem_block

theorem neg_step (P : Finset ℚ) (c sh sh' : ℚ) (t : ℕ) :
    ((P ∪ TPar.block c t).image (· + sh')).image Neg.neg =
      ((P.image (· + sh)).image Neg.neg).image (· + (sh - sh')) ∪ TPar.block (-c - sh') t := by
  ext x
  constructor
  · intro hx
    obtain ⟨_, hy, rfl⟩ := mem_image.1 hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
    rcases mem_union.1 hw with h | h
    · exact mem_union_left _ (mem_image.2 ⟨-(w + sh), mem_image.2 ⟨w + sh, mem_image.2 ⟨w, h, rfl⟩, rfl⟩, by ring⟩)
    · refine mem_union_right _ ?_
      have := neg_sub_mem_block (h := sh').2 h
      rwa [show -w - sh' = -(w + sh') by ring] at this
  · intro hx
    rcases mem_union.1 hx with h | h
    · obtain ⟨_, hy, rfl⟩ := mem_image.1 h
      obtain ⟨_, hy', rfl⟩ := mem_image.1 hy
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hy'
      exact mem_image.2 ⟨w + sh', mem_image.2 ⟨w, mem_union_left _ hw, rfl⟩, by ring⟩
    · refine mem_image.2 ⟨-x + -sh' + sh', mem_image.2 ⟨-x - sh', mem_union_right _ ?_, by ring⟩, by ring⟩
      refine (neg_sub_mem_block (h := sh')).1 ?_
      rwa [show -(-x - sh') - sh' = x by ring]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc)

theorem rank_top {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = rankX D j :=
  (G.isV (X := .top j) hj (fun _ h => by cases h)).rank

theorem rank_grid {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i D.R.m)).rank = rankV D i D.R.m := by
  cases i with
  | zero =>
    have e : G.node (.grid 0 D.R.m) = ⟨D.sp.X', L.ΛX⟩ := colY_m L
    show (G.node (.grid 0 D.R.m)).sp.rank = _
    rw [e]
    show D.sp.X'.rank = _
    rw [D.sp.X'_rank]
    simp [rankV, Ranks.rankX']
  | succ i =>
    exact (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)).rank

theorem rankV_pos (D : D7) (i j : ℕ) : 0 < rankV D i j := by
  have := D.R.m_add_three_le_k
  have : 0 < D.R.r := by unfold Ranks.r; omega
  simp only [rankV]
  omega

theorem rankX_pos (D : D7) (j : ℕ) : 0 < rankX D j := by
  simp only [rankX, rankP, nRk]
  omega

theorem extNu_of_step (p : Pair T) (ha : 0 < (G.V p.small).rank) (hab : (G.V p.small).rank ≤ (G.V p.big).rank)
    (hs : ∀ τ (r : Fin (G.V p.big).rank), (wt G p.big τ).natW r = if h : r.1 < (G.V p.small).rank then
      (wt G p.small τ).natW ⟨r.1, h⟩ + (wt G p.big τ).natW ⟨(G.V p.small).rank - 1, by omega⟩ else 0) (τ) (r) :
    (wt G p.big τ).natW r =
      extNu (G.V p.big).rank (fun τ r => (wt G p.small τ).natW r + nuEnd G p τ) τ r := by
  rw [hs τ r]
  simp only [extNu, nuEnd]
  split_ifs with h h'
  · rfl
  · omega
  · rfl

theorem rank_top_lt {j : ℕ} (hj : j + 1 ≤ D.R.m) : (G.V (.top j)).rank - 1 < (G.V (.top (j + 1))).rank := by
  have e : rankX D (j + 1) = rankX D j + (D.R.t + 1) := by simp only [rankX]; ring
  rw [rank_top G (j := j) (by omega), rank_top G hj, e]
  omega

theorem rank_grid_lt {i : ℕ} (hi : i + 1 ≤ D.R.m) :
    (G.V (.grid i D.R.m)).rank - 1 < (G.V (.grid (i + 1) D.R.m)).rank := by
  have e : rankV D (i + 1) D.R.m = rankV D i D.R.m + sLen D := by simp only [rankV]; ring
  have := (odd_sLen D).pos
  rw [rank_grid G (i := i) (by omega), rank_grid G hi, e]
  omega

variable (sc) in

theorem step_top {j : ℕ} (hj : j + 1 ≤ D.R.m) (τ : D.what₂.Tau) (r : Fin (G.V (.top (j + 1))).rank) :
    (wt G (.top (j + 1)) τ).natW r = if h : r.1 < (G.V (.top j)).rank then
      (wt G (.top j) τ).natW ⟨r.1, h⟩ + (wt G (.top (j + 1)) τ).natW ⟨(G.V (.top j)).rank - 1, rank_top_lt G hj⟩ else 0 := by
  have r0 := rank_top G (j := j) (by omega)
  have r1 := rank_top G (j := j + 1) hj
  have h0 := isHC_top D sc.cGap τ (j := j) (by omega) r0
  have h1 := isHC_top D sc.cGap τ hj r1
  have hE := h0.1.card_entries.trans h0.2.1
  have hF := h1.1.card_entries.trans h1.2.1
  have e0 : entries (Node.par D sc.cGap (.top j) τ) = (num D sc.cGap τ).weightX j := entries_plus _
  have e1 : entries (Node.par D sc.cGap (.top (j + 1)) τ) = (num D sc.cGap τ).weightX (j + 1) := entries_plus _
  refine natW_step (t := D.R.t + 1) ?_ (r0 ▸ rankX_pos D j) 0 (-((num D sc.cGap τ).e (j + 1) : ℚ)) hE ?_ ?_ hF _ _
    (fun r => wtOf_cast hE h0.2.2 r) (fun r => wtOf_cast hF h1.2.2 r) r
  · rw [r0, r1]
    simp only [rankX]
    ring
  · rw [e0, e1, GridData.weightX_succ]
    simp only [add_zero, image_id']
    rfl
  · rw [e0]
    intro x hx y hy
    rw [add_zero]
    exact weightX_above D sc.cGap τ hj hx hy

variable (sc) in

theorem step_grid {i : ℕ} (hi : i + 1 ≤ D.R.m) (τ : D.what₂.Tau) (r : Fin (G.V (.grid (i + 1) D.R.m)).rank) :
    (wt G (.grid (i + 1) D.R.m) τ).natW r = if h : r.1 < (G.V (.grid i D.R.m)).rank then
      (wt G (.grid i D.R.m) τ).natW ⟨r.1, h⟩ + (wt G (.grid (i + 1) D.R.m) τ).natW ⟨(G.V (.grid i D.R.m)).rank - 1, rank_grid_lt G hi⟩ else 0 := by
  have r0 := rank_grid G (i := i) (by omega)
  have r1 := rank_grid G (i := i + 1) hi
  have h0 := isHC_grid D sc.cGap τ (i := i) (by omega) r0
  have h1 := isHC_grid D sc.cGap τ hi r1
  have hA := h0.1.card_entries.trans h0.2.1
  have hA' := h1.1.card_entries.trans h1.2.1
  have hE : ((entries (Node.par D sc.cGap (.grid i D.R.m) τ)).image Neg.neg).card = (G.V (.grid i D.R.m)).rank := by
    rw [card_image_of_injective _ neg_injective, hA]
  have hF : ((entries (Node.par D sc.cGap (.grid (i + 1) D.R.m) τ)).image Neg.neg).card = (G.V (.grid (i + 1) D.R.m)).rank := by
    rw [card_image_of_injective _ neg_injective, hA']
  obtain ⟨sh, hsh⟩ : ∃ sh : ℚ, entries (Node.par D sc.cGap (.grid i D.R.m) τ) =
      (entries ((num D sc.cGap τ).parD i (num D sc.cGap τ).m)).image (· + sh) := ⟨_, entries_shift _ _⟩
  obtain ⟨sh', hsh'⟩ : ∃ sh' : ℚ, entries (Node.par D sc.cGap (.grid (i + 1) D.R.m) τ) =
      (entries ((num D sc.cGap τ).parD (i + 1) (num D sc.cGap τ).m)).image (· + sh') := ⟨_, entries_shift _ _⟩
  have hsucc : entries ((num D sc.cGap τ).parD (i + 1) (num D sc.cGap τ).m) =
      entries ((num D sc.cGap τ).parD i (num D sc.cGap τ).m) ∪
        TPar.block ((num D sc.cGap τ).cen ((num D sc.cGap τ).m - i) : ℚ) (num D sc.cGap τ).s :=
    entries_parD_succ D sc.cGap τ (j := (num D sc.cGap τ).m) hi
  refine natW_step (t := (num D sc.cGap τ).s) ?_ (r0 ▸ rankV_pos D i D.R.m) (sh - sh')
    (-((num D sc.cGap τ).cen ((num D sc.cGap τ).m - i) : ℚ) - sh') hE ?_ ?_ hF _ _ (fun r => ?_) (fun r => ?_) r
  · rw [r0, r1]
    show _ = _ + sLen D
    simp only [rankV]
    ring
  · rw [hsh, hsh', hsucc]
    exact neg_step _ _ _ _ _
  · intro x hx y hy
    rw [hsh] at hx
    obtain ⟨_, hx', rfl⟩ := mem_image.1 hx
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hx'
    have hy2 : -(-y - sh') - sh' ∈ TPar.block (-((num D sc.cGap τ).cen ((num D sc.cGap τ).m - i) : ℚ) - sh') (num D sc.cGap τ).s := by
      rw [show -(-y - sh') - sh' = y by ring]
      exact hy
    have hy' : -y - sh' ∈ (num D sc.cGap τ).blockC ((num D sc.cGap τ).m - i) := neg_sub_mem_block.1 hy2
    have := parD_below D sc.cGap τ hi hx₀ hy'
    show y < -(x₀ + sh) + (sh - sh')
    linarith
  · have e : ((wt G (.grid i D.R.m) τ).w r : ℚ) = -(((wtOf _ (entries (Node.par D sc.cGap (.grid i D.R.m) τ))).w r.rev : ℤ) : ℚ) := by
      show (((-(wtOf _ (entries (Node.par D sc.cGap (.grid i D.R.m) τ))).w r.rev : ℤ)) : ℚ) = _
      push_cast
      rfl
    rw [e, wtOf_cast hA h0.2.2, highestWeight_neg hA hE]
  · have e : ((wt G (.grid (i + 1) D.R.m) τ).w r : ℚ) = -(((wtOf _ (entries (Node.par D sc.cGap (.grid (i + 1) D.R.m) τ))).w r.rev : ℤ) : ℚ) := by
      show (((-(wtOf _ (entries (Node.par D sc.cGap (.grid (i + 1) D.R.m) τ))).w r.rev : ℤ)) : ℚ) = _
      push_cast
      rfl
    rw [e, wtOf_cast hA' h1.2.2, highestWeight_neg hA' hF]

theorem wtOK_of_defPair : ∀ p : Pair T, DefPair D.R.m p → WtOK G p := by
  intro p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ : i + 1 ≤ D.R.m ∧ j = D.R.m := hp
    have r0 := rank_grid G (i := i) (by omega)
    have r1 := rank_grid G (i := i + 1) hi
    have hlt : (G.V (.grid i D.R.m)).rank ≤ (G.V (.grid (i + 1) D.R.m)).rank := by
      rw [r0, r1]; simp only [rankV]; nlinarith [Nat.zero_le (sLen D)]
    refine ⟨fun τ => ⟨isHC_grid D sc.cGap τ (by omega) r0, isHC_grid D sc.cGap τ hi r1⟩,
      jet_in_vv_of_weight ℂ _ _ _ hlt _ _ _ (extNu_of_step G (.chi i D.R.m) (r0 ▸ rankV_pos D i D.R.m) hlt fun τ r => ?_)⟩
    exact step_grid sc G hi τ r
  | mu t i j => exact hp.elim
  | core i => exact hp.elim
  | top t j =>
    have hj : j + 1 ≤ D.R.m := hp
    have r0 := rank_top G (j := j) (by omega)
    have r1 := rank_top G (j := j + 1) hj
    have hlt : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank := by
      rw [r0, r1]; simp only [rankX]; nlinarith [Nat.zero_le D.R.t]
    refine ⟨fun τ => ⟨isHC_top D sc.cGap τ (by omega) r0, isHC_top D sc.cGap τ hj r1⟩,
      jet_in_vv_of_weight ℂ _ _ _ hlt _ _ _ (extNu_of_step G (.top t j) (r0 ▸ rankX_pos D j) hlt fun τ r => ?_)⟩
    exact step_top sc G hj τ r

end Final

end GlobalTheory.FunObj
