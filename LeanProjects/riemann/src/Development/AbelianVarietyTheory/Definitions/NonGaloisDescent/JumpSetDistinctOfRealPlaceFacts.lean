import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

structure JFacts (L : SizeData₂ D) (j : ℕ) (ρ : D.what₂.Tau) : Prop where
  hj1 : 1 ≤ j
  hjm : j ≤ D.R.m
  t_pos : 1 ≤ D.R.t
  t_odd : Odd D.R.t
  k_pos : 1 ≤ D.R.k - 1
  v_nonneg : ∀ a, 0 ≤ (D.hc ρ).v a
  v_le : ∀ a, (((D.hc ρ).v a : ℚ) : ℝ) ≤ L.Sc
  v_anti : ∀ a a' : Fin (D.R.k - 1), a.1 < a'.1 → (D.hc ρ).v a' < (D.hc ρ).v a
  b_mono : ∀ i i' : Fin D.R.m, i.1 < i'.1 → (D.hc ρ).b i < (D.hc ρ).b i'
  low_pos : ∀ i : Fin D.R.m, i.1 < j → ((D.R.t : ℚ) + 3) / 2 ≤ sz D j ρ - (D.hc ρ).b i
  low_neg : ∀ i : Fin D.R.m, j ≤ i.1 → sz D j ρ - (D.hc ρ).b i ≤ -(((D.R.t : ℚ) + 3) / 2)
  low_le : ∀ i, (((|sz D j ρ - (D.hc ρ).b i| : ℚ)) : ℝ) ≤ L.etaSz
  s_gt : L.etaSz + D.R.t + L.Sc < ((sz D j ρ : ℚ) : ℝ)
  s_le : ((sz D j ρ : ℚ) : ℝ) ≤ L.sc.b + L.etaSz + 1
  s_thick : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces → L.sc.b ≤ ((sz D j ρ : ℚ) : ℝ)
  par_b : L.etaSz + D.R.t + L.Sc ≤ L.sc.b
  t_le_eta : (D.R.t : ℝ) ≤ L.etaSz
  Sc_pos : 0 < L.Sc
  eta_pos : 0 < L.etaSz

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

section HC

variable {R : Ranks} (P : HCParam R)

theorem hc_u_anti : ∀ (i j : ℕ) (hi : i < R.k) (hj : j < R.k), i < j → P.u ⟨j, hj⟩ < P.u ⟨i, hi⟩ := by
  intro i j
  induction j with
  | zero => intro _ _ h; omega
  | succ j ih =>
    intro hi hj hij
    have step : P.u ⟨j + 1, hj⟩ < P.u ⟨j, by omega⟩ :=
      lt_trans (P.v_gt_u ⟨j, by omega⟩) (P.u_gt_v ⟨j, by omega⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact step.trans (ih hi (by omega) h)
    · subst h; exact step

theorem hc_v_anti (a a' : Fin (R.k - 1)) (h : a.1 < a'.1) : P.v a' < P.v a := by
  have h1 := P.u_gt_v a'
  have h2 := P.v_gt_u a
  have h3 : P.u ⟨a'.1, by omega⟩ ≤ P.u ⟨a.1 + 1, by omega⟩ := by
    rcases Nat.lt_or_ge (a.1 + 1) a'.1 with h4 | h4
    · exact le_of_lt (hc_u_anti P _ _ _ _ h4)
    · have : a'.1 = a.1 + 1 := by omega
      exact le_of_eq (congrArg P.u (Fin.ext this))
  exact lt_of_lt_of_le h1 (h3.trans (le_of_lt h2))

theorem hc_b_mono : ∀ (i j : ℕ) (hi : i < R.m) (hj : j < R.m), i < j → P.b ⟨i, hi⟩ < P.b ⟨j, hj⟩ := by
  intro i j
  induction j with
  | zero => intro _ _ h; omega
  | succ j ih =>
    intro hi hj hij
    have ht : (0 : ℚ) ≤ R.t := by positivity
    have step : P.b ⟨j, by omega⟩ < P.b ⟨j + 1, hj⟩ := by
      have h1 := P.gap_eb ⟨j, by omega⟩ hj
      have h2 := P.gap_be ⟨j, by omega⟩
      linarith
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih hi (by omega) h).trans step
    · subst h; exact step

theorem hc_b_mono' (i i' : Fin R.m) (h : i.1 < i'.1) : P.b i < P.b i' :=
  hc_b_mono P i.1 i'.1 i.2 i'.2 h

theorem hc_b_le (i i' : Fin R.m) (h : i.1 ≤ i'.1) : P.b i ≤ P.b i' := by
  rcases Nat.lt_or_ge i.1 i'.1 with h' | h'
  · exact le_of_lt (hc_b_mono' P i i' h')
  · exact le_of_eq (congrArg P.b (Fin.ext (by omega)))

theorem hc_low_pos (jj : Fin R.m) (i : Fin R.m) (h : i.1 ≤ jj.1) : ((R.t : ℚ) + 3) / 2 ≤ P.e jj - P.b i := by
  have := P.gap_be jj
  have := hc_b_le P i jj h
  linarith

theorem hc_low_neg (jj : Fin R.m) (i : Fin R.m) (h : jj.1 < i.1) : ((R.t : ℚ) + 3) / 2 ≤ P.b i - P.e jj := by
  have h1 := P.gap_eb jj (by omega)
  have h2 := hc_b_le P ⟨jj.1 + 1, by omega⟩ i (by simp; omega)
  linarith

end HC

theorem sz_eq (j : ℕ) (ρ : D.what₂.Tau) (h : j - 1 < D.R.m) : sz D j ρ = (D.hc ρ).e ⟨j - 1, h⟩ := by
  unfold sz; rw [dif_pos h]

theorem wj_eq (j : ℕ) (ρ : D.what₂.Tau) : wj D j ρ = ((sz D j ρ : ℚ) : ℝ) := by
  unfold wj sz; split_ifs <;> simp

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  unfold Scale.b' Scale.a Scale.X' Scale.b
  exact div_pos (mul_pos hx (Real.exp_pos _)) (Real.exp_pos _)

theorem w''_le_top (L : SizeData₂ D) : L.sc.w'' D.R.n ≤ L.sc.b' + L.sc.b' / L.sc.x := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb := b'_pos L
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n; exact_mod_cast D.R.toFrame.ord_pos
  have h1 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    apply div_le_div_of_nonneg_left hb.le hx
    nlinarith
  have h2 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb.le hx.le
  linarith

theorem sz_win {L : SizeData₂ D} (hP : AdmPar L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) (ρ : D.what₂.Tau) :
    L.sc.w'' D.R.n ≤ ((sz D j ρ : ℚ) : ℝ) ∧ ((sz D j ρ : ℚ) : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  have hw'' : 0 < L.sc.w'' D.R.n := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith
  rw [← wj_eq]
  by_cases hth : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
  · have := L.win_thick j hj1 hjm ρ hth
    constructor <;> linarith [this.1, this.2]
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · unfold Host.topPlaces at htop
    obtain ⟨t0, ht0, hg⟩ := Finset.mem_image.1 htop
    have hw := L.win_top j hj1 hjm ρ ⟨t0, ht0⟩ hg.symm
    have hb := L.bT_ge ⟨t0, ht0⟩
    have h3' := h3 ⟨t0, ht0⟩
    have := w''_le_top L
    have := L.etaSz_pos
    constructor <;> linarith [hw.1, hw.2]
  · have hthin : D.host.IsThin (D.eTau ρ : D.R.GG) := ⟨(D.eTau ρ).2, htop, hth⟩
    have hw := L.win_thin j hj1 hjm ρ hthin
    have := L.etaSz_pos
    constructor <;> linarith [hw.1, hw.2]

theorem jFacts_of {L : SizeData₂ D} (hP : AdmPar L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) (ρ : D.what₂.Tau) :
    JFacts L j ρ := by
  have hjj : j - 1 < D.R.m := by omega
  have hs := sz_eq j ρ hjj
  have hwin := sz_win hP j hj1 hjm ρ
  obtain ⟨h1, h2, h3, h4⟩ := hP
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hw'' : 0 < L.sc.w'' D.R.n := by linarith
  have htpos : 1 ≤ D.R.t := D.R.t_odd.pos
  refine
    { hj1 := hj1, hjm := hjm, t_pos := htpos, t_odd := D.R.t_odd,
      k_pos := by have := D.R.m_add_three_le_k; omega,
      v_nonneg := fun a => by exact_mod_cast (L.cloud_v ρ a).1,
      v_le := fun a => (L.cloud_v ρ a).2,
      v_anti := fun a a' h => hc_v_anti (D.hc ρ) a a' h,
      b_mono := fun i i' h => hc_b_mono' (D.hc ρ) i i' h,
      low_pos := fun i hi => by
        rw [hs]; exact hc_low_pos (D.hc ρ) ⟨j - 1, hjj⟩ i (by simp; omega),
      low_neg := fun i hi => by
        rw [hs]; have := hc_low_neg (D.hc ρ) ⟨j - 1, hjj⟩ i (by simp; omega); linarith,
      low_le := fun i => by
        have := L.be_close ρ i ⟨j - 1, hjj⟩
        rw [hs, abs_sub_comm]; push_cast at this ⊢; exact this,
      s_gt := by linarith [hwin.1],
      s_le := hwin.2,
      s_thick := fun h => by rw [← wj_eq]; exact (L.win_thick j hj1 hjm ρ h).1,
      par_b := by linarith,
      t_le_eta := h4, Sc_pos := hS, eta_pos := he }

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

lemma jp_cast_sub (t c : ℕ) (h : c < t) : ((t - 1 - c : ℕ) : ℚ) = (t : ℚ) - 1 - c := by
  have h1 : t - 1 - c + c + 1 = t := by omega
  have h2 : ((t - 1 - c : ℕ) : ℚ) + c + 1 = t := by exact_mod_cast h1
  linarith

lemma jp_t_one {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) : (1 : ℚ) ≤ D.R.t := by
  exact_mod_cast hF.t_pos

lemma jp_s_gt {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) :
    (D.R.t : ℚ) < sz D j ρ := by
  have h1 := hF.s_gt
  have h2 := hF.Sc_pos
  have h3 := hF.eta_pos
  have h4 : ((D.R.t : ℚ) : ℝ) < ((sz D j ρ : ℚ) : ℝ) := by push_cast; linarith
  exact_mod_cast h4

lemma jp_b_pos {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (i : Fin D.R.m) :
    0 < (D.hc ρ).b i := by
  have h1 := hF.low_le i
  have h2 := hF.s_gt
  have h3 := hF.Sc_pos
  have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  rw [Rat.cast_abs] at h1
  have h5 := (le_abs_self _).trans h1
  push_cast at h5
  have h6 : (0 : ℝ) < (((D.hc ρ).b i : ℚ) : ℝ) := by linarith
  exact_mod_cast h6

lemma jp_low_cases {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (i : Fin D.R.m) :
    ((D.R.t : ℚ) + 3) / 2 ≤ sz D j ρ - (D.hc ρ).b i ∨ sz D j ρ - (D.hc ρ).b i ≤ -(((D.R.t : ℚ) + 3) / 2) := by
  rcases lt_or_ge i.1 j with h | h
  · exact Or.inl (hF.low_pos i h)
  · exact Or.inr (hF.low_neg i h)

lemma jp_block_iff (q : ℚ) : q ∈ blockJ D ↔ ∃ c : ℕ, c < D.R.t ∧ q = c := Iff.rfl

lemma jp_refl_block (q : ℚ) (hq : q ∈ blockJ D) : refl D q ∈ blockJ D := by
  obtain ⟨c, hc, rfl⟩ := hq
  refine ⟨D.R.t - 1 - c, by omega, ?_⟩
  rw [jp_cast_sub _ _ hc]
  simp only [AdmissibleParameterJ.refl]

lemma jp_refl_refl (q : ℚ) : refl D (refl D q) = q := by
  simp only [AdmissibleParameterJ.refl]; ring

lemma jp_block_not_cloud {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (q : ℚ)
    (hq : q ∈ blockJ D) : q ∉ cloudJ D j ρ := by
  obtain ⟨c, hc, rfl⟩ := hq
  rintro ⟨a, ha⟩
  have h1 : (c : ℚ) + 1 ≤ D.R.t := by exact_mod_cast (show c + 1 ≤ D.R.t by omega)
  have h2 := jp_s_gt hF
  have h3 := hF.v_nonneg a
  have h4 := jp_t_one hF
  simp only [c0] at ha
  linarith

lemma jp_block_not_low {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (q : ℚ)
    (hq : q ∈ blockJ D) : q ∉ lowJ D j ρ := by
  obtain ⟨c, hc, rfl⟩ := hq
  rintro ⟨a, ha⟩
  have h1 : (c : ℚ) + 1 ≤ D.R.t := by exact_mod_cast (show c + 1 ≤ D.R.t by omega)
  have h0 : (0 : ℚ) ≤ c := Nat.cast_nonneg _
  simp only [c0] at ha
  rcases jp_low_cases hF a with h | h <;> linarith

theorem block_mem_iff (a : ℤ) : ((a : ℚ) ∈ blockJ D ↔ 0 ≤ a ∧ a < (D.R.t : ℤ)) := by
  rw [jp_block_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    have h' : a = (c : ℤ) := by exact_mod_cast h
    omega
  · rintro ⟨h0, h1⟩
    refine ⟨a.toNat, by omega, ?_⟩
    have h2 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
    exact_mod_cast h2.symm

theorem block_not_mem_JW {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (up : Bool) (q : ℚ)
    (hq : q ∈ blockJ D) : q ∉ JW D up j ρ := by
  have hr := jp_refl_block q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_ofPred_eq]
    rintro (h | h)
    · exact jp_block_not_cloud hF _ hr h
    · exact jp_block_not_low hF _ hr h
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union]
    rintro (h | h)
    · exact jp_block_not_cloud hF _ hq h
    · exact jp_block_not_low hF _ hq h

theorem block_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (q : ℚ) (hq : q ∈ blockJ D) : q ∈ JJ D up j ρ := by
  cases up
  · simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, reflS, Jp, Set.mem_union, Set.mem_ofPred_eq]
    exact Or.inr (jp_refl_block q hq)
  · simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inr hq

theorem JJ_iff_JW {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (up : Bool) (q : ℚ)
    (hq : q ∉ blockJ D) : q ∈ JJ D up j ρ ↔ q ∈ JW D up j ρ := by
  cases up
  · have hr : refl D q ∉ blockJ D := fun h => hq (by simpa [jp_refl_refl] using jp_refl_block _ h)
    simp only [JJ, JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Jm, reflS, Jp, Set.mem_union,
      Set.mem_ofPred_eq]
    tauto
  · simp only [JJ, JW, cloudT, lowT, ↓reduceIte, Jp, Set.mem_union]
    tauto

lemma jp_nodup {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) : (PPm D j ρ).Nodup := by
  have hs := jp_s_gt hF
  have ht := jp_t_one hF
  have hvi : Function.Injective fun a : Fin (D.R.k - 1) => (D.hc ρ).v a := by
    intro a a' h
    rcases Nat.lt_trichotomy a.1 a'.1 with h1 | h1 | h1
    · exact absurd h (ne_of_gt (hF.v_anti a a' h1))
    · exact Fin.ext h1
    · exact absurd h (ne_of_lt (hF.v_anti a' a h1))
  have hbi : Function.Injective fun a : Fin D.R.m => -(D.hc ρ).b a := by
    intro a a' h
    simp only [neg_inj] at h
    rcases Nat.lt_trichotomy a.1 a'.1 with h1 | h1 | h1
    · exact absurd h (ne_of_lt (hF.b_mono a a' h1))
    · exact Fin.ext h1
    · exact absurd h (ne_of_gt (hF.b_mono a' a h1))
  have hci : Function.Injective fun c : ℕ => -sz D j ρ + ((D.R.t : ℚ) + 1) / 2 - ((c : ℚ) + 1) := by
    intro c c' h
    have h' : (c : ℚ) = c' := by simp only at h; linarith
    exact_mod_cast h'
  unfold PPm
  refine Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Multiset.Nodup.map hvi Finset.univ.nodup,
    Multiset.Nodup.map hbi Finset.univ.nodup, ?_⟩, Multiset.Nodup.map hci (Finset.range _).nodup, ?_⟩
  · rw [Multiset.disjoint_left]
    intro x hx hy
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨i, hi⟩ := hy
    have h1 := hF.v_nonneg a
    have h2 := jp_b_pos hF i
    linarith
  · rw [Multiset.disjoint_left]
    intro x hx hy
    simp only [Multiset.mem_add, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Finset.mem_range] at hx hy
    obtain ⟨c, hc, rfl⟩ := hy
    have h1 : (c : ℚ) + 1 ≤ D.R.t := by exact_mod_cast (show c + 1 ≤ D.R.t by omega)
    have h0 : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    rcases hx with ⟨a, ha⟩ | ⟨i, hi⟩
    · have h2 := hF.v_nonneg a
      linarith
    · rcases jp_low_cases hF i with h | h <;> linarith

lemma jp_mem_iff {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (q : ℚ) :
    q - sz D j ρ - c0 D ∈ PPm D j ρ ↔ q ∈ Jp D j ρ := by
  unfold PPm
  simp only [Multiset.mem_add, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    Finset.mem_range, Jp, Set.mem_union, cloudJ, lowJ, blockJ, Set.mem_ofPred_eq, c0]
  constructor
  · rintro ((⟨a, ha⟩ | ⟨a, ha⟩) | ⟨c, hc, h⟩)
    · exact Or.inl (Or.inl ⟨a, by linarith⟩)
    · exact Or.inl (Or.inr ⟨a, by linarith⟩)
    · refine Or.inr ⟨D.R.t - 1 - c, by omega, ?_⟩
      rw [jp_cast_sub _ _ hc]
      linarith
  · rintro ((⟨a, ha⟩ | ⟨a, ha⟩) | ⟨c, hc, h⟩)
    · exact Or.inl (Or.inl ⟨a, by linarith⟩)
    · exact Or.inl (Or.inr ⟨a, by linarith⟩)
    · refine Or.inr ⟨D.R.t - 1 - c, by omega, ?_⟩
      rw [jp_cast_sub _ _ hc]
      linarith

open Classical in
theorem count_PPm {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (q : ℚ) :
    (PPm D j ρ).count (q - sz D j ρ - c0 D) = if q ∈ Jp D j ρ then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (jp_nodup hF)]
  by_cases h : q ∈ Jp D j ρ
  · rw [if_pos ((jp_mem_iff hF q).2 h), if_pos h]
  · rw [if_neg (mt (jp_mem_iff hF q).1 h), if_neg h]

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

section JB

variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}

lemma realPlace_jumpCenter_nonneg (F : JFacts L j ρ) : 0 ≤ c0 D := by
  have ht : (1:ℚ) ≤ D.R.t := by exact_mod_cast F.t_pos
  simp only [c0]; linarith

lemma realPlace_t_add_one_lt_size (F : JFacts L j ρ) : (D.R.t : ℚ) + 1 < sz D j ρ := by
  have h1 := F.s_gt
  have h2 := F.t_le_eta
  have h3 := F.Sc_pos
  have h4 : (1:ℝ) ≤ D.R.t := by exact_mod_cast F.t_pos
  have : (((D.R.t : ℚ) + 1 : ℚ) : ℝ) < ((sz D j ρ : ℚ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

lemma realPlace_etaSize_lt_size (F : JFacts L j ρ) : L.etaSz < ((sz D j ρ : ℚ) : ℝ) := by
  have h1 := F.s_gt
  have h3 := F.Sc_pos
  have h4 : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
  linarith

lemma jb_cloud (F : JFacts L j ρ) {q : ℚ} (hq : q ∈ cloudJ D j ρ) :
    sz D j ρ ≤ q - c0 D ∧ ((q - c0 D : ℚ) : ℝ) ≤ ((sz D j ρ : ℚ) : ℝ) + L.Sc := by
  obtain ⟨a, rfl⟩ := hq
  have h1 := F.v_nonneg a
  have h2 := F.v_le a
  refine ⟨by linarith, ?_⟩
  have e : ((sz D j ρ + (D.hc ρ).v a + c0 D - c0 D : ℚ) : ℝ) =
      ((sz D j ρ : ℚ) : ℝ) + (((D.hc ρ).v a : ℚ) : ℝ) := by push_cast; ring
  rw [e]; linarith

lemma jb_low (F : JFacts L j ρ) {q : ℚ} (hq : q ∈ lowJ D j ρ) :
    ((D.R.t : ℚ) + 3) / 2 ≤ |q - c0 D| ∧ ((|q - c0 D| : ℚ) : ℝ) ≤ L.etaSz := by
  obtain ⟨a, rfl⟩ := hq
  have e : sz D j ρ - (D.hc ρ).b a + c0 D - c0 D = sz D j ρ - (D.hc ρ).b a := by ring
  rw [e]
  refine ⟨?_, F.low_le a⟩
  by_cases ha : a.1 < j
  · exact le_trans (F.low_pos a ha) (le_abs_self _)
  · have := F.low_neg a (not_lt.mp ha)
    exact le_trans (by linarith) (neg_le_abs _)

lemma jb_block {q : ℚ} (hq : q ∈ blockJ D) : |q - c0 D| ≤ c0 D := by
  obtain ⟨c, hc, rfl⟩ := hq
  have h1 : (c : ℚ) + 1 ≤ D.R.t := by exact_mod_cast Nat.succ_le_of_lt hc
  have h2 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  rw [abs_le]; simp only [c0]; constructor <;> linarith

lemma jb_notin_cl (F : JFacts L j ρ) {x : ℚ} (hx : |x - c0 D| ≤ ((D.R.t : ℚ) + 1) / 2) :
    x ∉ cloudJ D j ρ ∪ lowJ D j ρ := by
  rintro (h | h)
  · have h1 := (jb_cloud F h).1
    have h2 := realPlace_t_add_one_lt_size F
    have h3 := le_abs_self (x - c0 D)
    have h4 : (0:ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · have h1 := (jb_low F h).1
    linarith

lemma jb_notin_Jp (F : JFacts L j ρ) {x : ℚ} (hx : |x - c0 D| = ((D.R.t : ℚ) + 1) / 2) :
    x ∉ Jp D j ρ := by
  rintro (h | h)
  · exact jb_notin_cl F hx.le h
  · have := jb_block h
    rw [hx] at this; simp only [c0] at this; linarith

lemma jb_refl_abs (q : ℚ) : |refl D q - c0 D| = |q - c0 D| := by
  have : refl D q - c0 D = -(q - c0 D) := by simp only [AdmissibleParameterJ.refl, c0]; ring
  rw [this, abs_neg]

lemma jb_Jp_bound (F : JFacts L j ρ) {q : ℚ} (hq : q ∈ Jp D j ρ) :
    ((|q - c0 D| : ℚ) : ℝ) ≤ L.sc.b + L.Sc + L.etaSz + 1 := by
  have hb := F.par_b
  have hS := F.Sc_pos
  have he := F.eta_pos
  have ht : (1:ℝ) ≤ D.R.t := by exact_mod_cast F.t_pos
  have hte := F.t_le_eta
  rcases hq with (hq | hq) | hq
  · obtain ⟨h1, h2⟩ := jb_cloud F hq
    have hs := F.s_le
    have hs0 : (0:ℚ) < sz D j ρ := by
      have := realPlace_t_add_one_lt_size F
      have : (0:ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith
    have h0 : (0:ℚ) ≤ q - c0 D := by linarith
    rw [abs_of_nonneg h0]; linarith
  · have := (jb_low F hq).2; linarith
  · have h1 := jb_block hq
    have h2 : ((c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by simp only [c0]; push_cast; ring
    have h3 : ((|q - c0 D| : ℚ) : ℝ) ≤ ((c0 D : ℚ) : ℝ) := by exact_mod_cast h1
    linarith

lemma jb_cloud_eq : cloudJ D j ρ = Set.range (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D) := by
  ext q; simp only [cloudJ, Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

lemma jb_low_eq : lowJ D j ρ = Set.range (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D) := by
  ext q; simp only [lowJ, Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

lemma jb_block_eq : blockJ D = Set.range (fun c : Fin D.R.t => ((c : ℕ) : ℚ)) := by
  ext q; simp only [blockJ, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨c.1, c.2, rfl⟩

lemma jb_cloud_inj (F : JFacts L j ρ) :
    Function.Injective (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D) := by
  intro a a' h
  have hv : (D.hc ρ).v a = (D.hc ρ).v a' := by simp only at h; linarith
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h1 | h1
  · have := F.v_anti _ _ h1; linarith
  · have := F.v_anti _ _ h1; linarith

lemma jb_low_inj (F : JFacts L j ρ) :
    Function.Injective (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D) := by
  intro a a' h
  have hv : (D.hc ρ).b a = (D.hc ρ).b a' := by simp only at h; linarith
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h1 | h1
  · have := F.b_mono _ _ h1; linarith
  · have := F.b_mono _ _ h1; linarith

lemma jb_block_inj : Function.Injective (fun c : Fin D.R.t => ((c : ℕ) : ℚ)) := by
  intro a b h; simp only at h; exact Fin.ext (by exact_mod_cast h)

end JB

theorem jumpSetBound_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ) : CloudCentreDistance L := by
  intro j hj1 hjm ρ
  have F := h j hj1 hjm ρ
  have hcl : (cloudJ D j ρ).ncard = D.R.k - 1 := by
    rw [jb_cloud_eq, Set.ncard_range_of_injective (jb_cloud_inj F)]; simp
  have hlo : (lowJ D j ρ).ncard = D.R.m := by
    rw [jb_low_eq, Set.ncard_range_of_injective (jb_low_inj F)]; simp
  have hbl : (blockJ D).ncard = D.R.t := by
    rw [jb_block_eq, Set.ncard_range_of_injective jb_block_inj]; simp
  have hfc : (cloudJ D j ρ).Finite := by rw [jb_cloud_eq]; exact Set.finite_range _
  have hfl : (lowJ D j ρ).Finite := by rw [jb_low_eq]; exact Set.finite_range _
  have hfb : (blockJ D).Finite := by rw [jb_block_eq]; exact Set.finite_range _
  have hd1 : Disjoint (cloudJ D j ρ) (lowJ D j ρ) := by
    rw [Set.disjoint_left]
    intro q hc hl
    have h1 := (jb_cloud F hc).1
    have h2 := (jb_low F hl).2
    have h3 : ((q - c0 D : ℚ) : ℝ) ≤ ((|q - c0 D| : ℚ) : ℝ) := by exact_mod_cast le_abs_self _
    have h4 : ((sz D j ρ : ℚ) : ℝ) ≤ ((q - c0 D : ℚ) : ℝ) := by exact_mod_cast h1
    have h5 := realPlace_etaSize_lt_size F
    linarith
  have hd2 : Disjoint (cloudJ D j ρ ∪ lowJ D j ρ) (blockJ D) := by
    rw [Set.disjoint_left]
    intro q hq hb
    have h1 := jb_block hb
    have hc := realPlace_jumpCenter_nonneg F
    apply jb_notin_cl F _ hq
    simp only [c0] at h1 ⊢; linarith
  refine ⟨fun q hq => ?_, fun q hq => jb_low F hq, fun q hq => jb_block hq, hcl, hlo, ?_⟩
  · obtain ⟨h1, h2⟩ := jb_cloud F hq
    exact ⟨by exact_mod_cast h1, h2⟩
  · unfold Jp
    rw [Set.ncard_union_eq hd2 (hfc.union hfl) hfb, Set.ncard_union_eq hd1 hfc hfl, hcl, hlo, hbl]
    have := F.k_pos
    unfold Ranks.nV Ranks.r
    omega

theorem jumpSetCloud_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ) : jcCondition L := by
  intro j hj1 hjm ρ
  have F := h j hj1 hjm ρ
  have hc0 : c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  have ht0 : (0:ℚ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro q ⟨a, rfl⟩
    have hl := F.low_le a
    push_cast at hl
    rw [abs_le] at hl
    by_cases ha : a.1 < j
    · right
      have := F.low_pos a ha
      constructor
      · rw [hc0]; linarith
      · push_cast; linarith [hl.2]
    · left
      have := F.low_neg a (not_lt.mp ha)
      constructor
      · push_cast; linarith [hl.1]
      · rw [hc0]; linarith
  · intro up
    have hm1 : |(-1 : ℚ) - c0 D| = ((D.R.t : ℚ) + 1) / 2 := by
      rw [hc0, abs_of_neg (by linarith)]; ring
    have ht : |(D.R.t : ℚ) - c0 D| = ((D.R.t : ℚ) + 1) / 2 := by
      rw [hc0, abs_of_pos (by linarith)]; ring
    cases up
    · simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, reflS, Set.mem_ofPred_eq]
      constructor
      · apply jb_notin_Jp F; rw [jb_refl_abs]; exact hm1
      · apply jb_notin_Jp F; rw [jb_refl_abs]; exact ht
    · simp only [JJ, ↓reduceIte]
      exact ⟨jb_notin_Jp F hm1, jb_notin_Jp F ht⟩
  · intro q hq
    have h1 := (jb_cloud F hq).1
    have h2 := realPlace_t_add_one_lt_size F
    have h3 := realPlace_jumpCenter_nonneg F
    linarith
  · apply jb_notin_cl F
    rw [zero_sub, abs_neg, abs_of_nonneg (realPlace_jumpCenter_nonneg F), hc0]; linarith

theorem jumpSetEta_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ)
    (hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b) (ht : 1 ≤ D.R.t) (hS : 0 < L.Sc) (he : 0 < L.etaSz) :
    JumpAbsoluteBound L := by
  have ht' : (1:ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hc0r : ((c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by simp only [c0]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj1 hjm ρ up q hq
    have F := h j hj1 hjm ρ
    have key : ((|q - c0 D| : ℚ) : ℝ) ≤ L.sc.b + L.Sc + L.etaSz + 1 := by
      cases up
      · simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, reflS, Set.mem_ofPred_eq] at hq
        have := jb_Jp_bound F hq
        rwa [jb_refl_abs] at this
      · simp only [JJ, ↓reduceIte] at hq
        exact jb_Jp_bound F hq
    have c0nn := realPlace_jumpCenter_nonneg F
    have tri : |q| ≤ |q - c0 D| + c0 D := by
      have := abs_sub_abs_le_abs_sub q (c0 D)
      rw [abs_of_nonneg c0nn] at this; linarith
    have tri' : ((|q| : ℚ) : ℝ) ≤ ((|q - c0 D| : ℚ) : ℝ) + ((c0 D : ℚ) : ℝ) := by exact_mod_cast tri
    rw [Rat.cast_abs] at tri'
    linarith
  · simp only [hJ]; rw [hc0r]; linarith
  · simp only [hJ]; have : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · simp only [hJ]; linarith

theorem jumpSetGap_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ) : ThickPlaceCloudSizes L := by
  intro j hj1 hjm ρ
  have F := h j hj1 hjm ρ
  have hst := realPlace_t_add_one_lt_size F
  have ht0 : (0:ℚ) ≤ D.R.t := Nat.cast_nonneg _
  have htr : (1:ℝ) ≤ D.R.t := by exact_mod_cast F.t_pos
  have hsle := F.s_le
  have he := F.eta_pos
  refine ⟨fun hth up u hu => ?_, fun up u hu => ?_⟩
  · have hsb := F.s_thick hth
    cases up
    · simp only [cloudT, Bool.false_eq_true, ↓reduceIte, dualS, reflS, Set.mem_ofPred_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have h1 := F.v_nonneg a
      have h2 := F.v_le a
      have h1r : (0:ℝ) ≤ (((D.hc ρ).v a : ℚ) : ℝ) := by exact_mod_cast h1
      have e : u = sz D j ρ + (D.hc ρ).v a - ((D.R.t : ℚ) + 1) / 2 := by
        simp only [AdmissibleParameterJ.refl, c0] at ha; linarith
      have hu' : |u| = sz D j ρ + (D.hc ρ).v a - ((D.R.t : ℚ) + 1) / 2 := by
        rw [abs_of_nonneg (by rw [e]; linarith)]; exact e
      rw [hu']; push_cast
      constructor <;> linarith
    · simp only [cloudT, ↓reduceIte, dualS, Set.mem_ofPred_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have h1 := F.v_nonneg a
      have h2 := F.v_le a
      have h1r : (0:ℝ) ≤ (((D.hc ρ).v a : ℚ) : ℝ) := by exact_mod_cast h1
      have e : u = -(sz D j ρ + (D.hc ρ).v a + ((D.R.t : ℚ) + 1) / 2) := by
        simp only [c0] at ha; linarith
      have hu' : |u| = sz D j ρ + (D.hc ρ).v a + ((D.R.t : ℚ) + 1) / 2 := by
        rw [e, abs_neg, abs_of_nonneg (by linarith)]
      rw [hu']; push_cast
      constructor <;> linarith
  · simp only [dualS, Set.mem_ofPred_eq, Set.mem_union] at hu
    have hblock : ∀ x : ℚ, -x - 1 ∈ blockJ D → ((|x| : ℚ) : ℝ) ≤ L.etaSz + D.R.t + 2 := by
      intro x hx
      obtain ⟨c, hc, hce⟩ := hx
      have h1 : (c : ℚ) + 1 ≤ D.R.t := by exact_mod_cast Nat.succ_le_of_lt hc
      have h2 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
      have hx' : |x| ≤ D.R.t := by
        rw [show x = -((c : ℚ) + 1) by linarith, abs_neg, abs_of_nonneg (by linarith)]; exact h1
      have : ((|x| : ℚ) : ℝ) ≤ ((D.R.t : ℚ) : ℝ) := Rat.cast_le.mpr hx'
      rw [Rat.cast_natCast] at this
      linarith
    cases up
    · simp only [lowT, Bool.false_eq_true, ↓reduceIte, reflS, Set.mem_ofPred_eq] at hu
      rcases hu with hu | hu
      · obtain ⟨a, ha⟩ := hu
        have hl := F.low_le a
        push_cast at hl
        rw [abs_le] at hl
        have e : u = (sz D j ρ - (D.hc ρ).b a) - ((D.R.t : ℚ) + 1) / 2 := by
          simp only [AdmissibleParameterJ.refl, c0] at ha; linarith
        rw [Rat.cast_abs, e, abs_le]; push_cast
        constructor <;> linarith [hl.1, hl.2]
      · exact hblock u hu
    · simp only [lowT, ↓reduceIte] at hu
      rcases hu with hu | hu
      · obtain ⟨a, ha⟩ := hu
        have hl := F.low_le a
        push_cast at hl
        rw [abs_le] at hl
        have e : u = -(sz D j ρ - (D.hc ρ).b a) - ((D.R.t : ℚ) + 1) / 2 := by
          simp only [c0] at ha; linarith
        rw [Rat.cast_abs, e, abs_le]; push_cast
        constructor <;> linarith [hl.1, hl.2]
      · exact hblock u hu

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

lemma jd_inj {n : ℕ} (f : Fin n → ℚ) (h : ∀ a a' : Fin n, a.1 < a'.1 → f a ≠ f a') :
    Function.Injective f := by
  intro a a' e
  by_contra hne
  have hv : a.1 ≠ a'.1 := fun hv => hne (Fin.ext hv)
  rcases Nat.lt_or_gt_of_ne hv with h1 | h1
  · exact h _ _ h1 e
  · exact h _ _ h1 e.symm

lemma jd_card_lt {m j : ℕ} (hj : j ≤ m) :
    (Finset.univ.filter (fun a : Fin m => a.1 < j)).card = j := by
  have : Finset.univ.filter (fun a : Fin m => a.1 < j) = Finset.univ.image (Fin.castLE hj) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      exact ⟨⟨a.1, ha⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩
      simp [b.2]
  rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hj), Finset.card_univ,
    Fintype.card_fin]

lemma jd_card_ge {m j : ℕ} (hj : j ≤ m) :
    (Finset.univ.filter (fun a : Fin m => j ≤ a.1)).card = m - j := by
  have hinj : Function.Injective (fun b : Fin (m - j) => (⟨j + b.1, by omega⟩ : Fin m)) := by
    intro b b' e
    have := congrArg Fin.val e
    simp only at this
    exact Fin.ext (by omega)
  have : Finset.univ.filter (fun a : Fin m => j ≤ a.1) =
      Finset.univ.image (fun b : Fin (m - j) => (⟨j + b.1, by omega⟩ : Fin m)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      exact ⟨⟨a.1 - j, by omega⟩, Fin.ext (by simp only; omega)⟩
    · rintro ⟨b, rfl⟩
      simp only
      omega
  rw [this, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma jd_ncard {n : ℕ} (f : Fin n → ℚ) (hf : Function.Injective f) (p : Fin n → Prop)
    [DecidablePred p] (S : Set ℚ) (hS : ∀ q, q ∈ S ↔ ∃ a, p a ∧ q = f a) :
    S.ncard = (Finset.univ.filter p).card := by
  have hS' : S = ↑((Finset.univ.filter p).image f) := by
    ext q
    rw [hS, Finset.mem_coe, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [hS', Set.ncard_coe_finset, Finset.card_image_of_injective _ hf]

lemma jd_ncard_union {n₁ n₂ : ℕ} (f : Fin n₁ → ℚ) (g : Fin n₂ → ℚ) (hf : Function.Injective f)
    (hg : Function.Injective g) (p : Fin n₂ → Prop) [DecidablePred p]
    (hfg : ∀ a b, f a ≠ g b) (S : Set ℚ)
    (hS : ∀ q, q ∈ S ↔ (∃ a, q = f a) ∨ ∃ b, p b ∧ q = g b) :
    S.ncard = n₁ + (Finset.univ.filter p).card := by
  have hS' : S = (↑(Finset.univ.image f) : Set ℚ) ∪ ↑((Finset.univ.filter p).image g) := by
    ext q
    rw [hS, Set.mem_union, Finset.mem_coe, Finset.mem_coe, Finset.mem_image, Finset.mem_image]
    simp only [Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨b, hb, rfl⟩
    · rintro (⟨a, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨b, hb, rfl⟩
  have hdisj : Disjoint (↑(Finset.univ.image f) : Set ℚ) ↑((Finset.univ.filter p).image g) := by
    rw [Finset.disjoint_coe, Finset.disjoint_left]
    intro q h1 h2
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at h1 h2
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, -, hb⟩ := h2
    exact hfg a b hb.symm
  rw [hS', Set.ncard_union_eq hdisj, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hg, Finset.card_univ,
    Fintype.card_fin]

section Core

variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}

lemma cloudJumpSet_true : cloudT D true j ρ = cloudJ D j ρ := rfl
lemma jd_cloudT_f : cloudT D false j ρ = reflS D (cloudJ D j ρ) := rfl
lemma lowJumpSet_true : lowT D true j ρ = lowJ D j ρ := rfl
lemma jd_lowT_f : lowT D false j ρ = reflS D (lowJ D j ρ) := rfl
lemma jumpUnion_true : JW D true j ρ = cloudJ D j ρ ∪ lowJ D j ρ := rfl
lemma jd_JW_f : JW D false j ρ = reflS D (cloudJ D j ρ) ∪ reflS D (lowJ D j ρ) := rfl

lemma one_le_jump_parameter (F : JFacts L j ρ) : (1 : ℚ) ≤ D.R.t := by exact_mod_cast F.t_pos

lemma jumpCount_t_add_one_lt_size (F : JFacts L j ρ) : (D.R.t : ℚ) + 1 < sz D j ρ := by
  have h1 := F.s_gt
  have h2 := F.t_le_eta
  have h3 := F.Sc_pos
  have h4 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast F.t_pos
  have : (((D.R.t : ℚ) + 1 : ℚ) : ℝ) < ((sz D j ρ : ℚ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

lemma jd_b (F : JFacts L j ρ) (a : Fin D.R.m) : 0 < (D.hc ρ).b a := by
  have h1 := F.s_gt
  have h2 := F.low_le a
  have h3 := F.Sc_pos
  have h5 : ((sz D j ρ - (D.hc ρ).b a : ℚ) : ℝ) ≤ ((|sz D j ρ - (D.hc ρ).b a| : ℚ) : ℝ) :=
    Rat.cast_le.mpr (le_abs_self _)
  have h6 : ((sz D j ρ - (D.hc ρ).b a : ℚ) : ℝ) = ((sz D j ρ : ℚ) : ℝ) - (((D.hc ρ).b a : ℚ) : ℝ) := by
    push_cast; ring
  have h4 : (0 : ℝ) ≤ D.R.t := by positivity
  have : (0 : ℝ) < (((D.hc ρ).b a : ℚ) : ℝ) := by linarith
  exact_mod_cast this

lemma jd_lneg (F : JFacts L j ρ) (a : Fin D.R.m) (h : j ≤ a.1) :
    sz D j ρ - (D.hc ρ).b a + c0 D ≤ -2 := by
  have := F.low_neg a h
  have hc : c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  linarith

lemma jd_lpos (F : JFacts L j ρ) (a : Fin D.R.m) (h : a.1 < j) :
    (D.R.t : ℚ) + 1 ≤ sz D j ρ - (D.hc ρ).b a + c0 D := by
  have := F.low_pos a h
  have hc : c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  linarith

lemma jd_cl (F : JFacts L j ρ) (a : Fin (D.R.k - 1)) :
    (D.R.t : ℚ) + 1 < sz D j ρ + (D.hc ρ).v a + c0 D := by
  have := F.v_nonneg a
  have := jumpCount_t_add_one_lt_size F
  have := one_le_jump_parameter F
  have hc : c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  linarith

lemma jd_cl_low (F : JFacts L j ρ) (a : Fin (D.R.k - 1)) (a' : Fin D.R.m) :
    sz D j ρ - (D.hc ρ).b a' + c0 D < sz D j ρ + (D.hc ρ).v a + c0 D := by
  have := F.v_nonneg a
  have := jd_b F a'
  linarith

end Core

theorem jumpSetDistinct_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ) : JumpLowsSignCount D := by
  intro j hj1 hjm ρ
  have F := h j hj1 hjm ρ
  have ht := one_le_jump_parameter F
  have iL : Function.Injective (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D) :=
    jd_inj _ (fun a a' hl e => by
      have := F.b_mono a a' hl; try dsimp only at e
      linarith)
  have iR : Function.Injective
      (fun a : Fin D.R.m => (D.R.t : ℚ) - 1 - (sz D j ρ - (D.hc ρ).b a + c0 D)) :=
    jd_inj _ (fun a a' hl e => by
      have := F.b_mono a a' hl; try dsimp only at e
      linarith)
  have iC : Function.Injective
      (fun a : Fin (D.R.k - 1) => (D.R.t : ℚ) - 1 - (sz D j ρ + (D.hc ρ).v a + c0 D)) :=
    jd_inj _ (fun a a' hl e => by
      have := F.v_anti a a' hl; try dsimp only at e
      linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (jd_ncard _ iL (fun a => j ≤ a.1) _ ?_).trans (jd_card_ge hjm)
    intro q
    simp only [lowJ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, rfl⟩, hq⟩
      refine ⟨a, ?_, rfl⟩
      by_contra hlt; push_neg at hlt
      have := jd_lpos F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, by have := jd_lneg F a ha; linarith⟩
  · refine (jd_ncard _ iL (fun a => a.1 < j) _ ?_).trans (jd_card_lt hjm)
    intro q
    simp only [lowJ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, rfl⟩, hq⟩
      refine ⟨a, ?_, rfl⟩
      by_contra hlt; push_neg at hlt
      have := jd_lneg F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, by have := jd_lpos F a ha; linarith⟩
  · refine (jd_ncard _ iR (fun a => a.1 < j) _ ?_).trans (jd_card_lt hjm)
    intro q
    simp only [jd_lowT_f, reflS, AdmissibleParameterJ.refl, lowJ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, ha⟩, hq⟩
      refine ⟨a, ?_, by linarith⟩
      by_contra hlt; push_neg at hlt
      have := jd_lneg F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by ring⟩, by have := jd_lpos F a ha; linarith⟩
  · refine (jd_ncard _ iR (fun a => j ≤ a.1) _ ?_).trans (jd_card_ge hjm)
    intro q
    simp only [jd_lowT_f, reflS, AdmissibleParameterJ.refl, lowJ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, ha⟩, hq⟩
      refine ⟨a, ?_, by linarith⟩
      by_contra hlt; push_neg at hlt
      have := jd_lpos F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by ring⟩, by have := jd_lneg F a ha; linarith⟩
  · refine (jd_ncard _ iL (fun a => j ≤ a.1) _ ?_).trans (jd_card_ge hjm)
    intro q
    simp only [jumpUnion_true, cloudJ, lowJ, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨(⟨a, rfl⟩ | ⟨a, rfl⟩), hq⟩
      · have := jd_cl F a; linarith
      · refine ⟨a, ?_, rfl⟩
        by_contra hlt; push_neg at hlt
        have := jd_lpos F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Or.inr ⟨a, rfl⟩, by have := jd_lneg F a ha; linarith⟩
  · refine (jd_ncard_union _ _ iC iR (fun a => a.1 < j) ?_ _ ?_).trans
      (by rw [jd_card_lt hjm])
    · intro a b e
      try dsimp only at e
      have := jd_cl_low F a b; linarith
    · intro q
      simp only [jd_JW_f, reflS, AdmissibleParameterJ.refl, cloudJ, lowJ, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨(⟨a, ha⟩ | ⟨a, ha⟩), hq⟩
        · exact Or.inl ⟨a, by linarith⟩
        · refine Or.inr ⟨a, ?_, by linarith⟩
          by_contra hlt; push_neg at hlt
          have := jd_lneg F a hlt; linarith
      · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact ⟨Or.inl ⟨a, by ring⟩, by have := jd_cl F a; linarith⟩
        · exact ⟨Or.inr ⟨a, by ring⟩, by have := jd_lpos F a ha; linarith⟩

theorem jumpSetFinal_of_realPlaceFacts {L : SizeData₂ D} (h : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ) : DualCloudSizes L := by
  intro j hj1 hjm ρ
  have F := h j hj1 hjm ρ
  have ht := one_le_jump_parameter F
  have hs := jumpCount_t_add_one_lt_size F
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast F.t_pos
  have hc : c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  have iL4 : Function.Injective
      (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D - D.R.t) :=
    jd_inj _ (fun a a' hl e => by
      have := F.b_mono a a' hl; try dsimp only at e
      linarith)
  have iC5 : Function.Injective
      (fun a : Fin (D.R.k - 1) => -(sz D j ρ + (D.hc ρ).v a + c0 D) - 1) :=
    jd_inj _ (fun a a' hl e => by
      have := F.v_anti a a' hl; try dsimp only at e
      linarith)
  have iL5 : Function.Injective
      (fun a : Fin D.R.m => -(sz D j ρ - (D.hc ρ).b a + c0 D) - 1) :=
    jd_inj _ (fun a a' hl e => by
      have := F.b_mono a a' hl; try dsimp only at e
      linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro up u hu
    cases up
    · simp only [dualS, jd_cloudT_f, reflS, AdmissibleParameterJ.refl, cloudJ, Set.mem_setOf_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have hv := F.v_le a
      have hv0 : (0 : ℝ) ≤ (((D.hc ρ).v a : ℚ) : ℝ) := by exact_mod_cast F.v_nonneg a
      have hu' : u = sz D j ρ + (D.hc ρ).v a - ((D.R.t : ℚ) + 1) / 2 := by linarith
      have hpos : 0 < u := by have := F.v_nonneg a; linarith
      rw [abs_of_pos hpos]
      subst hu'
      push_cast
      constructor <;> linarith
    · simp only [dualS, cloudJumpSet_true, cloudJ, Set.mem_setOf_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have hv := F.v_le a
      have hv0 : (0 : ℝ) ≤ (((D.hc ρ).v a : ℚ) : ℝ) := by exact_mod_cast F.v_nonneg a
      have hu' : u = -(sz D j ρ + (D.hc ρ).v a + ((D.R.t : ℚ) + 1) / 2) := by linarith
      have hneg : u < 0 := by have := F.v_nonneg a; linarith
      rw [abs_of_neg hneg]
      subst hu'
      push_cast
      constructor <;> linarith
  · intro up u hu
    cases up
    · simp only [dualS, jd_lowT_f, reflS, AdmissibleParameterJ.refl, lowJ, Set.mem_setOf_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have hl := F.low_le a
      rw [Rat.cast_abs, abs_le] at hl
      have hu' : u = sz D j ρ - (D.hc ρ).b a - ((D.R.t : ℚ) + 1) / 2 := by linarith
      subst hu'
      push_cast at hl ⊢
      constructor <;> linarith [hl.1, hl.2]
    · simp only [dualS, lowJumpSet_true, lowJ, Set.mem_setOf_eq] at hu
      obtain ⟨a, ha⟩ := hu
      have hl := F.low_le a
      rw [Rat.cast_abs, abs_le] at hl
      have hu' : u = -(sz D j ρ - (D.hc ρ).b a) - ((D.R.t : ℚ) + 1) / 2 := by linarith
      subst hu'
      push_cast at hl ⊢
      constructor <;> linarith [hl.1, hl.2]
  · intro up hu
    cases up
    · simp only [dualS, jd_JW_f, reflS, AdmissibleParameterJ.refl, cloudJ, lowJ, Set.mem_union,
        Set.mem_setOf_eq] at hu
      rcases hu with ⟨a, ha⟩ | ⟨a, ha⟩
      · have := jd_cl F a; linarith
      · by_cases hja : j ≤ a.1
        · have := jd_lneg F a hja; linarith
        · have := jd_lpos F a (by omega); linarith
    · simp only [dualS, jumpUnion_true, cloudJ, lowJ, Set.mem_union, Set.mem_setOf_eq] at hu
      rcases hu with ⟨a, ha⟩ | ⟨a, ha⟩
      · have := jd_cl F a; linarith
      · by_cases hja : j ≤ a.1
        · have := jd_lneg F a hja; linarith
        · have := jd_lpos F a (by omega); linarith
  · refine (jd_ncard _ iL4 (fun a => j ≤ a.1) _ ?_).trans (jd_card_ge hjm)
    intro u
    simp only [dualS, jd_JW_f, reflS, AdmissibleParameterJ.refl, cloudJ, lowJ, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨(⟨a, ha⟩ | ⟨a, ha⟩), hu⟩
      · have := jd_cl F a; linarith
      · refine ⟨a, ?_, by linarith⟩
        by_contra hlt; push_neg at hlt
        have := jd_lpos F a hlt; linarith
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Or.inr ⟨a, by ring⟩, by have := jd_lneg F a ha; linarith⟩
  · refine (jd_ncard_union _ _ iC5 iL5 (fun a => a.1 < j) ?_ _ ?_).trans
      (by rw [jd_card_lt hjm])
    · intro a b e
      try dsimp only at e
      have := jd_cl_low F a b; linarith
    · intro u
      simp only [dualS, jumpUnion_true, cloudJ, lowJ, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨(⟨a, ha⟩ | ⟨a, ha⟩), hu⟩
        · exact Or.inl ⟨a, by linarith⟩
        · refine Or.inr ⟨a, ?_, by linarith⟩
          by_contra hlt; push_neg at hlt
          have := jd_lneg F a hlt; linarith
      · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact ⟨Or.inl ⟨a, by ring⟩, by have := jd_cl F a; linarith⟩
        · exact ⟨Or.inr ⟨a, by ring⟩, by have := jd_lpos F a ha; linarith⟩

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical

variable {D : D7}

theorem cc_mul_cc' (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem mul_cc_mem_Psi' {φ : Formalism.HC.Frame} {g : φ.GG} (hg : g ∉ φ.Psi) :
    g * φ.cc ∈ φ.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
  show g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h
  · exact absurd h hg
  · rw [h]; rfl

theorem exists_placeOf (g : D.R.GG) : ∃ ρ : D.what₂.Tau, PlaceOf D ρ g := by
  by_cases hgP : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨g, hgP⟩, Or.inl (by simp)⟩
  · refine ⟨D.eTau.symm ⟨g * D.R.cc, mul_cc_mem_Psi' hgP⟩, Or.inr ?_⟩
    simp [mul_assoc, cc_mul_cc']

theorem count_key {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau} (hF : JFacts L j ρ) (J : Multiset ℤ) (sg : ℚ)
    (cτ c : ℤ) (up : Bool) (hsU : up = true → sg = 1) (hsD : up = false → sg = -1)
    (hJ : J.map (fun n : ℤ => (n : ℚ)) = (PPm D j ρ).map (fun p => sg * p + cτ))
    (hc : (c : ℚ) = sg * (-sz D j ρ) - c0 D + cτ) (a : ℤ) :
    ((J.count (a + c) : ℕ) : ℤ) = if (a : ℚ) ∈ JJ D up j ρ then 1 else 0 := by
  have hinj : Function.Injective (fun n : ℤ => (n : ℚ)) := Int.cast_injective
  have hsg2 : sg = 1 ∨ sg = -1 := by cases up <;> simp_all
  have hfinj : Function.Injective (fun p : ℚ => sg * p + cτ) := by
    intro p q h
    rcases hsg2 with rfl | rfl <;> simp only at h <;> linarith
  have h1 : J.count (a + c) = (J.map (fun n : ℤ => (n : ℚ))).count ((a + c : ℤ) : ℚ) :=
    (Multiset.count_map_eq_count' _ _ hinj _).symm
  have hp0 : sg * (sg * ((a : ℚ) + c - cτ)) + cτ = ((a + c : ℤ) : ℚ) := by
    push_cast; rcases hsg2 with rfl | rfl <;> ring
  rw [h1, hJ, ← hp0, Multiset.count_map_eq_count' _ _ hfinj]
  cases up
  · have hs := hsD rfl
    subst hs
    have : (-1 : ℚ) * ((a : ℚ) + c - cτ) = ((D.R.t : ℚ) - 1 - a) - sz D j ρ - c0 D := by
      rw [hc]; unfold c0; ring
    rw [this, count_PPm hF]
    have hr : AdmissibleParameterJ.refl D (a : ℚ) = (D.R.t : ℚ) - 1 - a := rfl
    have hm : ((a : ℚ) ∈ JJ D false j ρ) ↔ ((D.R.t : ℚ) - 1 - a ∈ Jp D j ρ) := by
      show AdmissibleParameterJ.refl D (a : ℚ) ∈ Jp D j ρ ↔ _
      rw [hr]
    by_cases h : (D.R.t : ℚ) - 1 - a ∈ Jp D j ρ
    · rw [if_pos h, if_pos (hm.2 h)]; simp
    · rw [if_neg h, if_neg (fun h' => h (hm.1 h'))]; simp
  · have hs := hsU rfl
    subst hs
    have : (1 : ℚ) * ((a : ℚ) + c - cτ) = (a : ℚ) - sz D j ρ - c0 D := by
      rw [hc]; ring
    rw [this, count_PPm hF]
    simp only [JJ, if_true]
    split_ifs <;> simp

theorem ite_ne_zero_iff' (P : Prop) [Decidable P] : ((if P then (1 : ℤ) else 0) ≠ 0) ↔ P := by
  by_cases h : P <;> simp [h]

theorem dualS_int (S : Set ℚ) (a : ℤ) : ((a : ℚ) ∈ dualS S ↔ ((-a - 1 : ℤ) : ℚ) ∈ S) := by
  simp only [dualS, Set.mem_setOf_eq]; push_cast; rfl

theorem jumpLemma_a_of_admissible {L : SizeData₂ D} (hP : AdmPar L) (hG2 : DeRhamFamilyAway D) (hCr : CrysIffWD D.nd D.naut)
    (hG2g : DeRhamFamilyTypePrimes D) (hDi : AdmDict D) (hRd : AdmRead D) : ConclusionJa D := by
  obtain ⟨ep, hdict⟩ := hDi
  refine ⟨ep, ?_⟩
  intro i r hr w hw C τ
  obtain ⟨hInd, ⟨g, hg⟩, hread⟩ := hRd i r hr w hw C τ
  obtain ⟨ρ, hρ⟩ := exists_placeOf (D := D) g
  have hRA : ReadAt D i (gEmb C τ) g ρ := ⟨hg, hρ⟩
  obtain ⟨sg, cτ, hsU, hsD, hJ0, hchi⟩ := hdict i (gEmb C τ) g ρ hRA
  obtain ⟨hχdR, hχJ⟩ := hchi w hInd
  rw [Multiset.map_eq_singleton] at hχJ
  obtain ⟨c, hc, hcq⟩ := hχJ
  have hjr := D.nd.j_range i
  have hF := jFacts_of hP (D.nd.j i) hjr.1 hjr.2 ρ
  set up := decide (TypeU D ep g) with hup
  have hsU' : up = true → sg = 1 := fun h => hsU (by simpa [hup] using h)
  have hsD' : up = false → sg = -1 := fun h => hsD (by simpa [hup] using h)
  have hx : ∀ x, D.naut.IsdRW i (rQ D i r x) w ∧
      D.naut.jumpsW i (rQ D i r x) (gEmb C τ) = D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ) := by
    intro x
    by_cases hl : D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1
    · have h := hG2g i r hr hl w hw x
      exact ⟨h.1, h.2 _ hInd⟩
    · push Not at hl
      have h := (hG2 i r hr w hw).1 hl.1 hl.2 x
      have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      exact ⟨((hCr i _ _ w hw hcont).1 h.1).1, h.2 _ hInd⟩
  have hkey : ∀ a : ℤ, (((D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ)).count (a + c) : ℕ) : ℤ) =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 :=
    count_key hF _ sg cτ c up hsU' hsD' hJ0 hcq

  have hTw : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).1, (hx x).2, hkey]
  have hDu : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
      if (a : ℚ) ∈ dualS (JJ D up (D.nd.j i) ρ) then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).2, (hx x).2, dualS_int, ← hkey]
    congr 3; ring
  refine ⟨g, ρ, hRA, ?_, ?_⟩
  · intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    refine ⟨?_, hTw x a, ?_, hDu x a⟩
    · rw [h2 _ (Or.inl rfl) a, hTw x a]; exact ite_ne_zero_iff' _
    · rw [h2 _ (Or.inr rfl) a, hDu x a]; exact ite_ne_zero_iff' _
  · intro ρπ π hπ hdec a
    obtain ⟨h1, h2, h3⟩ := hread π (hx π).1 hχdR c hc
    have hW : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ JW D up (D.nd.j i) ρ then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).1, hTw π a]
      by_cases hb : (a : ℚ) ∈ blockJ D
      · have hb' := (block_mem_iff (D := D) a).1 hb
        rw [if_pos (block_sub_JJ up _ ρ _ hb), if_pos hb', if_neg (block_not_mem_JW hF up _ hb)]
        simp
      · have hb' : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hb ((block_mem_iff a).2 h)
        rw [if_neg hb', sub_zero]
        simp only [JJ_iff_JW hF up _ hb]
    have hT : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ dualS (JW D up (D.nd.j i) ρ) then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).2.1, hW, dualS_int]
    refine ⟨?_, hW a, ?_, hT a⟩
    · rw [(h3 ρπ hπ hdec a).2.2.1, hW a]; exact ite_ne_zero_iff' _
    · rw [(h3 ρπ hπ hdec a).2.2.2, hT a]; exact ite_ne_zero_iff' _

end GlobalTheory.JumpSets

end

noncomputable section

namespace GlobalTheory.JumpSets

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ

theorem stmtJ_holds (D : D7) : JumpBoundClosedForm D := by
  intro L hA
  obtain ⟨hG2, hCr, hG2g, hDi, hRd, hP⟩ := hA
  have hF : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ := fun j h1 h2 ρ => jFacts_of hP j h1 h2 ρ
  have hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith [hP.1, hP.2.1]
  exact ⟨jumpLemma_a_of_admissible hP hG2 hCr hG2g hDi hRd, jumpSetBound_of_realPlaceFacts hF, jumpSetCloud_of_realPlaceFacts hF, jumpSetDistinct_of_realPlaceFacts hF,
    jumpSetEta_of_realPlaceFacts hF hpar D.R.t_odd.pos L.Sc_pos L.etaSz_pos, jumpSetFinal_of_realPlaceFacts hF, jumpSetGap_of_realPlaceFacts hF⟩

end GlobalTheory.JumpSets

end
