import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.GlobalSchurBounds.AlcoveOf

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem lam_entry (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℚ) = flipTwoThree.lamLiftN D u τ a.1 := by
  rw [(D.fm u).lam_eq i hi τ a]
  unfold flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ
  by_cases h : a.1 < D.R.k
  · simp [h]
  · have hj : (a.1 - D.R.k) / (D.R.t + 1) < D.R.m := D.R.blk_lt hi a h
    simp [h, hj]

theorem lam_entryR (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = ((flipTwoThree.lamLiftN D u τ a.1 : ℚ) : ℝ) := by
  rw [← lam_entry D u i hi τ a]
  norm_cast

theorem wJ_mono {D : D7} {u : D.what₂.Word} {τ : D.what₂.Tau}
    (h : ∀ j, j + 1 < D.R.m → flipTwoThree.wJ D u τ j ≤ flipTwoThree.wJ D u τ (j + 1)) (c : ℕ) (hc : c < D.R.m) :
    flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ c := by
  induction c with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (ih (by omega)) (h n hc)

theorem top_not_thick (D : D7) (τ : D.what₂.Tau) (h : flipTwoThree.IsTop D τ) : ¬ flipTwoThree.IsThick D τ := by
  unfold flipTwoThree.IsTop at h
  unfold flipTwoThree.IsThick
  unfold Host.topPlaces at h
  unfold Host.thickPlaces
  intro h2
  rw [Finset.mem_image] at h h2
  obtain ⟨a, ha, hae⟩ := h
  obtain ⟨s, hs, hse⟩ := h2
  rw [← hse] at hae
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Prod.mk.injEq] at hae
  exact absurd hae.1.1 (by decide)

theorem nums_basic {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (u : D.what₂.Word) (hN : NumsL D L Cn cL) :
    L.Sc ≤ L.sc.b' ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.b' ∧ 0 < L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ 24 * L.sc.x ≤ L.sc.b' := by
  obtain ⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, _⟩ := hN u
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNn : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (11 : ℝ) ≤ D.R.t := by
    have h1 := D.R.rank_add_five_le
    have h2 := D.R.m_add_three_le_k
    have h3 := D.R.two_le_m
    have : 11 ≤ D.R.t := by omega
    exact_mod_cast this
  have hmt : (22 : ℝ) ≤ D.R.m * D.R.t := by nlinarith
  have hq : 24 ≤ L.sc.b' / L.sc.x := by linarith
  have hb24 : 24 * L.sc.x ≤ L.sc.b' := by rwa [le_div_iff₀ hx0] at hq
  have hb0 : 0 < L.sc.b' := by nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0.le (by linarith)
  have hbb : L.sc.b' ≤ L.sc.b := by
    rwa [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne'] at n6
  refine ⟨by nlinarith, ?_, hb0, hbb, hb24⟩
  have h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hNn
  linarith

theorem entry_top_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (hτ : τ ∈ topsOf D.host D.eTau) (i : ℕ) (hi' : i ≤ D.R.m) (a : Fin (D.R.N i))
    (ha0 : a.1 ≠ 0) : |((((D.fm u).lam i τ).w a : ℤ) : ℝ)| ≤ 2 * L.sc.b' := by
  have htop : flipTwoThree.IsTop D τ := by
    unfold topsOf at hτ
    exact (Finset.mem_filter.mp hτ).2
  obtain ⟨hScb, -, hb'pos, -, -⟩ := nums_basic hcL u hN
  obtain ⟨-, hTop, -, hmono, hthin, -, hk1, -⟩ := hW u τ
  obtain ⟨-, -, hb1, hb2, hmid⟩ := hTop htop
  have hthick : ¬ flipTwoThree.IsThick D τ := top_not_thick D τ htop
  rw [lam_entryR D u i hi' τ a]
  unfold flipTwoThree.lamLiftN
  split_ifs with hak
  · by_cases hlast : a.1 = D.R.k - 1
    · rw [hlast]
      rw [abs_le]
      constructor <;> linarith
    · have h0 : 0 < a.1 := Nat.pos_of_ne_zero ha0
      have hlt : a.1 < D.R.k - 1 := by omega
      obtain ⟨hl, hu⟩ := hmid a.1 h0 hlt
      rw [abs_le]
      constructor <;> linarith
  · set j := (a.1 - D.R.k) / (D.R.t + 1) with hj
    have hjm : j < D.R.m := D.R.blk_lt hi' a hak
    have hup : (flipTwoThree.wJ D u τ j : ℝ) ≤ 2 * L.sc.b' := hthin hthick j hjm
    have hmon : flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ j := wJ_mono hmono j hjm
    have hlowR : ((-(flipTwoThree.lamCol D u τ (D.R.k - 1)) : ℚ) : ℝ) ≤ (flipTwoThree.wJ D u τ j : ℝ) := by
      exact_mod_cast hk1.trans hmon
    push_cast at hlowR ⊢
    rw [abs_le]
    constructor <;> linarith

theorem shift_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (u : D.what₂.Word) (i : ℕ)
    (hi : i ≤ D.R.m) : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ L.sc.b' := by
  have h1 : i * (D.R.t + 1) / 2 ≤ D.R.N D.R.m :=
    calc i * (D.R.t + 1) / 2 ≤ i * (D.R.t + 1) := Nat.div_le_self _ _
      _ ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hi
      _ ≤ D.R.k + D.R.m * (D.R.t + 1) := Nat.le_add_left _ _
      _ = D.R.N D.R.m := rfl
  have h2 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h1
  exact h2.trans (nums_basic hcL u hN).2.1

theorem Wt_top_le {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (hτ : τ ∈ topsOf D.host D.eTau) : (product_first_zeroth_parts.Wt D u τ : ℝ) ≤ 3 * L.sc.b' := by
  obtain ⟨-, -, hb'pos, -, -⟩ := nums_basic hcL u hN
  have habs : ∀ z : ℤ, ∀ n : ℕ, |(z : ℝ)| ≤ 2 * L.sc.b' → (n : ℝ) ≤ L.sc.b' →
      (((z - (n : ℤ)).natAbs : ℕ) : ℝ) ≤ 3 * L.sc.b' := by
    intro z n hz hn
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_le] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have key : product_first_zeroth_parts.Wt D u τ ≤ ⌊3 * L.sc.b'⌋₊ := by
    unfold product_first_zeroth_parts.Wt Wtau
    apply Finset.sup_le
    intro i hi
    apply Finset.sup_le
    intro a _
    have hi' : i ≤ D.R.m := by
      have := Finset.mem_range.mp hi
      omega
    split_ifs with h0
    · exact Nat.zero_le _
    · have ha0 : a.1 ≠ 0 := fun h => h0 ⟨h, hτ⟩
      apply Nat.le_floor
      exact habs _ _ (entry_top_le hcL hN hW u τ hτ i hi' a ha0) (shift_le hcL hN u i hi')
  calc (product_first_zeroth_parts.Wt D u τ : ℝ) ≤ (⌊3 * L.sc.b'⌋₊ : ℝ) := by exact_mod_cast key
    _ ≤ 3 * L.sc.b' := Nat.floor_le (by linarith)

theorem N_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]

theorem aTop_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (((D.fm u).aTop τ : ℤ) : ℝ) = ((flipTwoThree.lamCol D u τ 0 : ℚ) : ℝ) := by
  have hk : 0 < D.R.k := by
    have h0 := D.R.N_pos 0
    rwa [N_zero] at h0
  have h := lam_entryR D u 0 (Nat.zero_le _) τ ⟨0, D.R.N_pos 0⟩
  simp only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h
  unfold MemberForms.aTop
  exact h

theorem bTop_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (((D.fm u).bTop τ : ℤ) : ℝ) = -((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hN : 0 < D.R.N 0 := D.R.N_pos 0
  have hk : D.R.N 0 - 1 < D.R.k := by
    have h0 := hN
    rw [N_zero] at h0 ⊢
    omega
  have h := lam_entryR D u 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩
  simp only [flipTwoThree.lamLiftN, Fin.val_mk, hk, ↓reduceIte] at h
  unfold MemberForms.bTop DomWeight.detShift
  rw [dif_pos hN]
  push_cast
  rw [h, N_zero]

theorem amax_le {D : D7} {L : SizeData₂ D} {Cn : ℝ} (hW : WtsL D L Cn) (u : D.what₂.Word) :
    (product_first_zeroth_parts.amax D u : ℝ) ≤ 2 * L.sc.a := by
  have key : product_first_zeroth_parts.amax D u ≤ ⌊2 * L.sc.a⌋ := by
    unfold product_first_zeroth_parts.amax
    rw [Finset.fold_max_le]
    refine ⟨?_, fun τ hτ => ?_⟩
    · rw [Int.le_floor]
      push_cast
      unfold Scale.a
      exact mul_nonneg (by norm_num) (mul_nonneg (by linarith [L.sc.one_lt_alt]) (Real.exp_pos _).le)
    · have htop : flipTwoThree.IsTop D τ := by
        unfold product_first_zeroth_parts.tops topsOf at hτ
        exact (Finset.mem_filter.mp hτ).2
      rw [Int.le_floor, aTop_eq]
      have h := ((hW u τ).2.1 htop).2.1
      unfold Scale.a
      exact h
  exact Int.le_floor.mp key

theorem card_VV_le (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : (product_first_zeroth_parts.VV D u w).card ≤ D.host.TT.card := by
  classical
  unfold product_first_zeroth_parts.VV LT.VVT
  split_ifs with hs
  · refine le_trans (Finset.card_le_card_of_injOn (t := topsOf D.host D.eTau) ((D.fm u).tauOf w)
      (fun v hv => ?_) (fun a _ b _ hab => ((D.fm u).tauOf w).injective hab)) ?_
    · simp only [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      exact hv.2
    · refine le_trans (Finset.card_le_card_of_injOn (t := D.host.topPlaces)
        (fun τ => ((D.eTau τ : D.R.Psi) : D.R.GG)) (fun τ hτ => ?_)
        (fun a _ b _ hab => D.eTau.injective (Subtype.ext hab))) ?_
      · unfold topsOf at hτ
        simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
        exact hτ.2
      · unfold Host.topPlaces
        exact Finset.card_image_le
  · simp

theorem mem_VV_top (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) (hv : v ∈ product_first_zeroth_parts.VV D u w) :
    (D.fm u).tauOf w v ∈ topsOf D.host D.eTau := by
  classical
  unfold product_first_zeroth_parts.VV LT.VVT at hv
  split_ifs at hv with hs
  · exact (Finset.mem_filter.mp hv).2
  · simp at hv

theorem fifthLevelSizes_of_weights {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn) :
    LevelPrimeSizeBounds D L 9 := by
  unfold LevelPrimeSizeBounds
  intro u w _
  obtain ⟨-, hNb, hb'pos, -, -⟩ := nums_basic hcL u hN
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have ha0 : 0 ≤ L.sc.a := by
    unfold Scale.a
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hak : 0 ≤ L.sc.a / D.R.k := div_nonneg ha0 (Nat.cast_nonneg _)
  have hkN : (D.R.k : ℝ) ≤ L.sc.b' := by
    have h1 : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    have h2 : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h1
    linarith
  have hamax : (product_first_zeroth_parts.amax D u : ℝ) / D.R.k ≤ 2 * (L.sc.a / D.R.k) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (amax_le hW u) hk0
  have hterm : ∀ v ∈ product_first_zeroth_parts.VV D u w, ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤ 9 * (L.sc.a / D.R.k + L.sc.b') := by
    intro v hv
    have htops := mem_VV_top D u w v hv
    have hWt := Wt_top_le hcL hN hW u _ htops
    have htop : flipTwoThree.IsTop D ((D.fm u).tauOf w v) := by
      unfold topsOf at htops
      exact (Finset.mem_filter.mp htops).2
    have hb2 := ((hW u ((D.fm u).tauOf w v)).2.1 htop).2.2.2.1
    have hbt := bTop_eq D u ((D.fm u).tauOf w v)
    linarith
  calc _ ≤ (product_first_zeroth_parts.VV D u w).card • (9 * (L.sc.a / D.R.k + L.sc.b')) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((product_first_zeroth_parts.VV D u w).card : ℝ) * (9 * (L.sc.a / D.R.k + L.sc.b')) := nsmul_eq_mul _ _
    _ ≤ (D.host.TT.card : ℝ) * (9 * (L.sc.a / D.R.k + L.sc.b')) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact_mod_cast card_VV_le D u w
    _ = 9 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') := by
        unfold LocalQuadraticParts.nTT
        ring

theorem levelPrime_setting_of_sizes {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 3 ≤ cL) (hN : NumsL D L Cn cL) (hW : WtsL D L Cn)
    (hT : L.TuGe) (hm : 4 ≤ D.R.m) (u : D.what₂.Word) : product_first_zeroth_parts.HidaSetting D u := by
  obtain ⟨_, s2, s3, s4, s5⟩ := nums_basic (by linarith) u hN
  have hx1 := L.sc.one_lt_alt
  have hb24 : 24 ≤ L.sc.b := by linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  have hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b := sq _
  have h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right hb24 (by linarith)
  have hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ) := by
    refine le_trans ?_ (hT u)
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    push_cast
    linarith
  refine ⟨?_, ⟨?_, GlobalTheoryTheory.Alc.alcove_of (by linarith) hN hW hT hm u⟩, fun τ hτ => ?_⟩
  · have hf : (D.R.f : ℝ) ≤ D.R.N D.R.m := by
      have h1 := D.R.f_le_k
      have : D.R.f ≤ D.R.N D.R.m := by unfold Ranks.f Ranks.n Ranks.N; omega
      exact_mod_cast this
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have h3 : 3 * (D.R.N D.R.m : ℝ) ≤ L.sc.b := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, n11, _⟩ := hN u
      have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
      have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have h1 : (D.R.N D.R.m : ℝ) * 3 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hN0
      linarith
    have hfN : (D.R.f : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) * D.R.N D.R.m := mul_le_mul_of_nonneg_right hf hN0
    have h9 : (3 * (D.R.N D.R.m : ℝ)) * (3 * (D.R.N D.R.m : ℝ)) ≤ L.sc.b * L.sc.b :=
      mul_le_mul h3 h3 (by linarith) (by linarith)
    have : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < ((D.mem u).A.T : ℝ) := by nlinarith
    exact_mod_cast this
  · have h1 := amax_le hW u
    have ha : L.sc.a = L.sc.x * L.sc.b := rfl
    have h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right (s5.trans s4) (by linarith)
    have : (4 * (product_first_zeroth_parts.amax D u : ℝ)) < ((D.mem u).A.T : ℝ) := by nlinarith
    exact_mod_cast this
  · have hTp : flipTwoThree.IsTop D τ := (Finset.mem_filter.1 hτ).2
    obtain ⟨_, w2, _⟩ := hW u τ
    have e3 := (w2 hTp).2.2.1
    have : (0 : ℝ) ≤ ((D.fm u).bTop τ : ℤ) := by rw [bTop_eq]; linarith
    exact_mod_cast this

theorem family_levelPrime_summary_closed {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hT : TuSize Fm) (hDl : DlSize Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C)) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hT⟩ := hT
  obtain ⟨x2, hE⟩ := hE
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  refine family_levelPrime_summary_simple Fm C 9 (by norm_num)
    ⟨max (max x0 x1) (max (max x2 x3) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : x ≥ x1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e4 : 4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1
    rw [hsx] at z1
    have : (4 : ℝ) ≤ (Fm.D x i).R.m := le_trans (h3 x e3) z1
    exact_mod_cast this
  exact ⟨(hE x e2 i).1, (hE x e2 i).2, fifthLevelSizes_of_weights (by norm_num) (hN x e0 i).1 (hN x e0 i).2,
    levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm⟩

end Formalism.MainNotions.J

end
