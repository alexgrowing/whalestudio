import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge Formalism.QuantumDeterminants

theorem std_drop {N : ℕ} (f : Fin N → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (h : ∀ (s : ℕ) (hs : s + 1 < N), g < f ⟨s, by omega⟩ - f ⟨s + 1, hs⟩) :
    ∀ a b : Fin N, a < b → g < f a - f b := by
  have key : ∀ (d a : ℕ) (hh : a + d + 1 < N), g < f ⟨a, by omega⟩ - f ⟨a + d + 1, hh⟩ := by
    intro d
    induction d with
    | zero => intro a hh; exact h a hh
    | succ d ih =>
      intro a hh
      have h1 := ih a (by omega)
      have h2 := h (a + d + 1) (by omega)
      have e : (⟨a + (d + 1) + 1, hh⟩ : Fin N) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      linarith
  intro a b hab
  have hlt : a.val < b.val := hab
  obtain ⟨d, hd⟩ : ∃ d, b.val = a.val + d + 1 := ⟨b.val - a.val - 1, by omega⟩
  have := key d a.val (by have := b.isLt; omega)
  have eb : b = ⟨a.val + d + 1, by have := b.isLt; omega⟩ := Fin.ext hd
  rw [eb]
  exact this

theorem std_two_rS (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Ranks.rS]
  omega

theorem std_lamD_cloud (D : D7) (τ : D.what₂.Tau) (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : s.val < D.R.k - 1) :
    lamD D τ s = vOne D τ (s.val + 1) := by
  have h2 : 1 ≤ s.val + 1 ∧ s.val + 1 ≤ D.R.k - 1 := ⟨by omega, by omega⟩
  unfold lamD lamSH lamS vOne
  rw [dif_pos h2]
  simp only [Fin.val_cast]
  rw [dif_pos h]
  rfl

theorem std_lamD_node (D : D7) (τ : D.what₂.Tau) (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ s.val < D.R.k - 1) :
    lamD D τ s = -bOne D τ (s.val - (D.R.k - 1) + 1) := by
  have hm := std_two_rS D
  have hk := D.R.m_add_three_le_k
  have h3 : s.val - (D.R.k - 1) < D.R.m := by have := s.isLt; omega
  have h2 : 1 ≤ s.val - (D.R.k - 1) + 1 ∧ s.val - (D.R.k - 1) + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  unfold lamD lamSH lamS bOne
  rw [dif_pos h2]
  simp only [Fin.val_cast]
  rw [dif_neg h, dif_pos h3]
  rfl

theorem std_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k) :
    uS D w τ i = uOne D w τ (i.val + 1) := by
  have h2 : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ D.R.k := ⟨by omega, by have := i.isLt; omega⟩
  unfold uOne
  rw [dif_pos h2]
  rfl

section Rec

variable (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem std_castN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]

theorem std_castM : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by rw [std_two_rS]

theorem std_L_ge : 1 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le

theorem std_b_gt : 1 < large₂.sc.b := by
  unfold Scale.b
  have := std_L_ge D large₂
  exact Real.one_lt_exp_iff.2 (by linarith)

theorem std_log_b : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _

variable {D large₂}

theorem std_gapAll (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b →
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 < lamD D τ a - lamD D τ b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgap, _, _, hCl⟩ := H.1
  refine std_drop _ _ (by positivity) (fun s hs => ?_)
  exact hgap τ ⟨s, by have := dimS_eq D.R; omega⟩ (by have := dimS_eq D.R; simp only; omega)

theorem std_anti (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) : StrictAnti (lamD D τ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCl⟩ := H.1
  intro a b hab
  have := std_gapAll H τ a b hab
  have h0 : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
  linarith

theorem std_isHC (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) : IsHCParam (lamD D τ) := by
  refine ⟨std_anti H τ, fun a => ?_⟩
  obtain ⟨t, ht⟩ := D.R.k_even
  have hN : (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((D.R.rS + t : ℕ) : ℝ) := by
    rw [ht]; push_cast; ring
  rw [hN]
  by_cases h : a.val < D.R.k - 1
  · rw [std_lamD_cloud D τ a h]
    unfold vOne
    rw [dif_pos ⟨by omega, by omega⟩]
    obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨a.val + 1 - 1, by omega⟩
    refine ⟨z - (D.R.rS + t : ℕ), ?_⟩
    rw [hz]; push_cast; ring
  · rw [std_lamD_node D τ a h]
    have hm := std_two_rS D
    have hk := D.R.m_add_three_le_k
    have h3 : a.val - (D.R.k - 1) < D.R.m := by have := a.isLt; omega
    unfold bOne
    rw [dif_pos ⟨by omega, by omega⟩]
    obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨a.val - (D.R.k - 1) + 1 - 1, by omega⟩
    refine ⟨-z - (D.R.rS + t : ℕ), ?_⟩
    rw [hz]; push_cast; ring

theorem std_interlace (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    InterlaceS (by omega) (uS D w τ) (lamD D τ) := by
  obtain ⟨_, _, _, _, _, _, hI, _⟩ := H.2.1
  exact ⟨fun i hi => (hI w τ).1 i hi, fun h0 => (hI w τ).2 h0⟩

end Rec

section Rec2

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem std_r_add (D : D7) : (D.R.r : ℝ) + 1 = (D.R.k : ℝ) + D.R.m := by
  have h : D.R.r + 1 = D.R.k + D.R.m := by
    have := D.R.two_le_m
    unfold Ranks.r; omega
  exact_mod_cast h

theorem std_Del_pos (D : D7) : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos

theorem std_sizes (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) :
    (8 : ℝ) ≤ D.R.m ∧ (D.R.m : ℝ) ≤ D.R.k ∧ 8 * (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ (D.R.k : ℝ) ^ 2 ≤ (D.s.Del : ℝ) ∧
      (1 : ℝ) ≤ D.R.f := by
  obtain ⟨_, _, h3, _, _, _, h7, _, _, _, _, _, _, _, _, _, _, _, _, h20, _, _, _, h24, _⟩ := H.1
  have hL := std_L_ge D large₂
  have hm8 : (8 : ℝ) ≤ D.R.m := le_trans hCl h24
  have hmk := m_le_k D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
    exact_mod_cast this
  have hk8 : 8 * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    refine le_trans ?_ h7
    have : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL
    nlinarith [sq_nonneg (D.R.m : ℝ)]
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  refine ⟨hm8, hmk, hk8, ?_, hf⟩
  refine le_trans ?_ h20
  have hbase : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by
    have : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * D.R.f := le_mul_of_one_le_right (by linarith) hf
    exact le_trans this (le_mul_of_one_le_right (by positivity) hL)
  have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := le_trans hk1 hbase
  calc (D.R.k : ℝ) ^ 2 ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ 2 := by gcongr
    _ = ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ (2 : ℝ) := by norm_cast
    _ ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

theorem std_cloud_bd (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) (τ : D.what₂.Tau)
    (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : s.val < D.R.k - 1) :
    0 ≤ lamD D τ s ∧ lamD D τ s ≤ bOne D τ 1 / 8 := by
  obtain ⟨_, _, _, _, _, _, _, h8, _⟩ := H.1
  obtain ⟨d1, _⟩ := H.2.1
  obtain ⟨hm8, _, _, _, _⟩ := std_sizes H hCl
  rw [std_lamD_cloud D τ s h]
  have hv := d1 τ (s.val + 1) (by omega) (by omega)
  have hb := h8 τ 1 le_rfl (by have := D.R.two_le_m; omega)
  have hD := std_Del_pos D
  have hkD : 0 ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := by positivity
  have h64 : 64 ≤ Cl * (D.R.m : ℝ) := by nlinarith
  refine ⟨hv.1, ?_⟩
  have : 64 * ((D.R.k : ℝ) * (D.s.Del : ℝ)) ≤ bOne D τ 1 := by
    refine le_trans ?_ hb
    have := mul_le_mul_of_nonneg_right h64 hkD
    nlinarith
  have hv2 := hv.2
  linarith

theorem std_first_node (D : D7) (τ : D.what₂.Tau) :
    lamD D τ ⟨D.R.k - 1, by have := D.R.m_add_three_le_k; omega⟩ = -bOne D τ 1 := by
  rw [std_lamD_node D τ _ (by simp)]
  simp

theorem std_last_node (D : D7) (τ : D.what₂.Tau) :
    lamD D τ ⟨2 * D.R.rS + D.R.k, by omega⟩ = -bOne D τ D.R.m := by
  have hm := std_two_rS D
  have hk := D.R.m_add_three_le_k
  rw [std_lamD_node D τ _ (by simp only; omega)]
  congr 2
  simp only
  omega

theorem std_node_bd (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau)
    (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ s.val < D.R.k - 1) :
    -2 * bOne D τ 1 ≤ lamD D τ s ∧ lamD D τ s ≤ -bOne D τ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17, _⟩ := H.1
  have ha := (std_anti H τ).antitone
  have h1 : lamD D τ s ≤ lamD D τ ⟨D.R.k - 1, by have := D.R.m_add_three_le_k; omega⟩ :=
    ha (Fin.le_def.2 (by simp only; omega))
  have h2 : lamD D τ ⟨2 * D.R.rS + D.R.k, by omega⟩ ≤ lamD D τ s :=
    ha (Fin.le_def.2 (by have := s.isLt; simp only; omega))
  rw [std_first_node] at h1
  rw [std_last_node] at h2
  have := h17 τ
  exact ⟨by linarith, h1⟩

theorem std_isCloud {k n : ℕ} {hkn : k ≤ n} {u : Fin k → ℝ} {lam : Fin n → ℝ} (hI : InterlaceS hkn u lam)
    (s : Fin n) (h : s.val + 1 < k) : IsCloud u lam s :=
  ⟨⟨⟨s.val, by omega⟩, (hI.1 s.val h).1⟩, ⟨⟨s.val + 1, h⟩, (hI.1 s.val h).2⟩⟩

theorem std_cut {k : ℕ} (u u' : Fin k → ℝ) (i : Fin k) (V De : ℝ)
    (h : (u i = V ∧ u' i = V - De) ∨ (u i = V - De ∧ u' i = V)) (hD : 4 ≤ De) :
    IsCutS u u' (Set.Icc (-V + 2) (-V + De - 2)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨i, _, _, by rw [h1, h2]; intro e; linarith, by linarith, rfl, ?_, ?_, ?_⟩
    · rw [h1, h2]; exact min_lt_iff.2 (Or.inl (by linarith))
    · rw [h1, h2]; exact lt_max_iff.2 (Or.inr (by linarith))
    · intro y hy
      rw [h1, h2]
      exact ⟨le_abs.2 (Or.inl (by linarith [hy.1])), le_abs.2 (Or.inr (by linarith [hy.2]))⟩
  · refine ⟨i, _, _, by rw [h1, h2]; intro e; linarith, by linarith, rfl, ?_, ?_, ?_⟩
    · rw [h1, h2]; exact min_lt_iff.2 (Or.inr (by linarith))
    · rw [h1, h2]; exact lt_max_iff.2 (Or.inl (by linarith))
    · intro y hy
      rw [h1, h2]
      exact ⟨le_abs.2 (Or.inr (by linarith [hy.2])), le_abs.2 (Or.inl (by linarith [hy.1]))⟩

theorem vertex_difference_eq (D : D7) (τ : D.what₂.Tau) : vOne D τ 1 - vOne D τ 2 = 4 * (D.s.Del : ℝ) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have h := D.s.cloud_gap D.u₀ τ 0 (by omega)
  rw [D.hcW_v] at h
  unfold vOne
  rw [dif_pos ⟨le_rfl, by omega⟩, dif_pos ⟨by omega, by omega⟩]
  exact_mod_cast h

end Rec2

section Rec3

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem std_nc_idx (D : D7) (a b : Fin (2 * D.R.rS + D.R.k + 1)) (hab : a < b)
    (he : epsSH D.R a ≠ epsSH D.R b) : D.R.k - 1 < b.val := by
  by_contra hcon
  have hlt : a.val < b.val := hab
  have ha : a.val < D.R.k - 1 := by omega
  apply he
  have ea : epsSH D.R a = true := by
    unfold epsSH epsS
    simp only [Fin.val_cast]
    rw [if_pos ha]
  have eb : epsSH D.R b = true := by
    unfold epsSH epsS
    simp only [Fin.val_cast]
    by_cases hb : b.val < D.R.k - 1
    · rw [if_pos hb]
    · rw [if_neg hb]
      have : b.val - (D.R.k - 1) = 0 := by omega
      exact decide_eq_true (by rw [this])
  rw [ea, eb]

theorem std_ncgap (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamD D τ) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h21, _⟩ := H.1
  have ha := (std_anti H τ).antitone
  have hm := std_two_rS D
  have hk := D.R.m_add_three_le_k
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤ lamD D τ a - lamD D τ b := by
    intro a b hab he
    have hb := std_nc_idx D a b hab he
    have hlt : a.val < b.val := hab
    have hbl := b.isLt
    have h1 : lamD D τ ⟨b.val - 1, by omega⟩ ≤ lamD D τ a := ha (Fin.le_def.2 (by simp only; omega))
    rw [std_lamD_node D τ ⟨b.val - 1, by omega⟩ (by simp only; omega)] at h1
    rw [std_lamD_node D τ b (by omega)]
    have h2 := h21 τ (b.val - 1 - (D.R.k - 1) + 1) (by omega) (by omega)
    have e : b.val - 1 - (D.R.k - 1) + 1 + 1 = b.val - (D.R.k - 1) + 1 := by omega
    rw [e] at h2
    simp only at h1
    linarith
  intro a b he
  rcases lt_trichotomy a b with h | h | h
  · exact le_trans (key a b h he) (le_abs_self _)
  · exact absurd (by rw [h]) he
  · rw [abs_sub_comm]
    exact le_trans (key b a h (Ne.symm he)) (le_abs_self _)

theorem std_kaS (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) :
    0 < kaS D ∧ kaS D ≤ 1 ∧ (kaS D)⁻¹ ≤ large₂.sc.b ^ (1 / 8 + 2 * Cg) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, h12, h13, h14, h15, _, _, _, h19, _⟩ := H.1
  obtain ⟨hm8, hmk, _, _, _⟩ := std_sizes H hCl
  have hb := std_b_gt D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hL := std_L_ge D large₂
  have hkb : (8 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hkb8 : (8 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    calc (8 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := hkb
      _ = ((D.R.k : ℝ) * large₂.sc.b) ^ 1 := (pow_one _).symm
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hg0 : (8 : ℝ) ≤ (D.host.g 0 : ℝ) := le_trans hkb8 h12
  have hg1 : (8 : ℝ) ≤ (D.host.g 1 : ℝ) := le_trans hkb8 h14
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hrd : 2 ≤ D.host.rdE := by rw [hv] at h19; linarith
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have hka : kaS D = Real.pi / (D.host.rdE / 2) / ((D.host.g 0 : ℝ) * D.host.g 1) := rfl
  have hgg : (64 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith
  have hrdb : D.host.rdE ≤ large₂.sc.b ^ ((1 : ℝ) / 8) := by
    rw [Real.le_rpow_iff_log_le (by linarith) hb0, std_log_b]
    refine le_trans h11 ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨by rw [hka]; positivity, ?_, ?_⟩
  · rw [hka, div_div, div_le_one (by positivity)]
    have h1 : (1 : ℝ) * 64 ≤ D.host.rdE / 2 * ((D.host.g 0 : ℝ) * D.host.g 1) :=
      mul_le_mul (by linarith) hgg (by norm_num) (by linarith)
    linarith
  · have hinv : (kaS D)⁻¹ = D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) / (2 * Real.pi) := by
      rw [hka]
      have : D.host.rdE ≠ 0 := by linarith
      have : (D.host.g 0 : ℝ) ≠ 0 := by linarith
      have : (D.host.g 1 : ℝ) ≠ 0 := by linarith
      field_simp
    rw [hinv]
    have e : large₂.sc.b ^ (1 / 8 + 2 * Cg) = large₂.sc.b ^ ((1 : ℝ) / 8) * (large₂.sc.b ^ Cg * large₂.sc.b ^ Cg) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; congr 1; ring
    rw [e]
    have h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ large₂.sc.b ^ Cg * large₂.sc.b ^ Cg :=
      mul_le_mul h13 h15 (by linarith) (by positivity)
    have h2 : D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) ≤
        large₂.sc.b ^ ((1 : ℝ) / 8) * (large₂.sc.b ^ Cg * large₂.sc.b ^ Cg) :=
      mul_le_mul hrdb h1 (by positivity) (by positivity)
    exact le_trans (div_le_self (by positivity) (by linarith)) h2

theorem first_node_size_bounds (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) (τ : D.what₂.Tau) :
    (D.R.k : ℝ) ^ 8 ≤ bOne D τ 1 ∧ bOne D τ 1 ≤ large₂.sc.b ^ (2 : ℝ) / 1 ∧ 2 * bOne D τ 1 ≤ 2 * large₂.sc.b ^ (2 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h16, _⟩ := H.1
  obtain ⟨hm8, hmk, _, _, _⟩ := std_sizes H hCl
  have h := h16 τ 1 le_rfl (by have := D.R.two_le_m; omega)
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  refine ⟨?_, by simpa using h.2, by linarith [h.2]⟩
  calc (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ (8 : ℝ) := by norm_cast
    _ ≤ (D.R.k : ℝ) ^ Cl := Real.rpow_le_rpow_of_exponent_le hk1 hCl
    _ ≤ bOne D τ 1 := le_trans (le_max_left _ _) h.1

end Rec3

section Rec4

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem std_allGaps (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) (X : ℝ)
    (hX : X ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) : AllGaps (lamD D τ) X := by
  intro s s' hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact le_trans (le_trans hX (std_gapAll H τ s s' h).le) (le_abs_self _)
  · rw [abs_sub_comm]
    exact le_trans (le_trans hX (std_gapAll H τ s' s h).le) (le_abs_self _)

theorem std_lam_abs (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) (τ : D.what₂.Tau)
    (s : Fin (2 * D.R.rS + D.R.k + 1)) : |lamD D τ s| ≤ large₂.sc.b ^ (2 : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h16, _⟩ := H.1
  obtain ⟨hm8, hmk, _, _, _⟩ := std_sizes H hCl
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  by_cases h : s.val < D.R.k - 1
  · obtain ⟨h1, h2⟩ := std_cloud_bd H hCl τ s h
    obtain ⟨h3, h4, _⟩ := first_node_size_bounds H hCl τ
    have h5 : 0 ≤ bOne D τ 1 := le_trans (by positivity) h3
    rw [abs_of_nonneg h1]
    simp only [div_one] at h4
    linarith
  · have hm := std_two_rS D
    have hk := D.R.m_add_three_le_k
    have hs := s.isLt
    rw [std_lamD_node D τ s h, abs_neg]
    have h1 := h16 τ (s.val - (D.R.k - 1) + 1) (by omega) (by omega)
    have h2 : 0 ≤ bOne D τ (s.val - (D.R.k - 1) + 1) :=
      le_trans (by positivity) (le_trans (le_max_left _ _) h1.1)
    rw [abs_of_nonneg h2]
    exact h1.2

theorem std_u_abs (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) (w : D.what₂.Word) (τ : D.what₂.Tau)
    (i : Fin D.R.k) : |uS D w τ i| ≤ max (large₂.sc.b ^ (2 : ℝ)) (large₂.sc.b ^ Cu) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, _⟩ := H.1
  have hI := std_interlace H w τ
  have hk := D.R.m_add_three_le_k
  have hil := i.isLt
  rw [abs_le]
  constructor
  · by_cases h : i.val + 1 < D.R.k
    · have h1 := (hI.1 i.val h).1
      have h2 := (std_cloud_bd H hCl τ ⟨i.val, by omega⟩ (by simp only; omega)).1
      have h3 : 0 ≤ max (large₂.sc.b ^ (2 : ℝ)) (large₂.sc.b ^ Cu) :=
        le_trans (Real.rpow_nonneg (by have := std_b_gt D large₂; linarith) _) (le_max_left _ _)
      have e : (⟨i.val, by omega⟩ : Fin D.R.k) = i := Fin.ext rfl
      rw [e] at h1
      linarith
    · have h1 := hI.2 (by omega)
      have e : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = i := Fin.ext (by simp only; omega)
      rw [e] at h1
      have h2 := std_lam_abs H hCl τ ⟨D.R.k - 1, by omega⟩
      have h3 := (abs_le.1 h2).1
      have h4 := le_max_left (large₂.sc.b ^ (2 : ℝ)) (large₂.sc.b ^ Cu)
      linarith
  · by_cases h : i.val = 0
    · have h1 := h18 w τ
      rw [std_uS, h]
      exact le_trans h1 (le_max_right _ _)
    · have h1 := (hI.1 (i.val - 1) (by omega)).2
      have e : (⟨i.val - 1 + 1, by omega⟩ : Fin D.R.k) = i := Fin.ext (by simp only; omega)
      rw [e] at h1
      have h2 := std_lam_abs H hCl τ ⟨i.val - 1, by omega⟩
      have h3 := (abs_le.1 h2).2
      have h4 := le_max_left (large₂.sc.b ^ (2 : ℝ)) (large₂.sc.b ^ Cu)
      linarith

theorem std_shape (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hCl : 8 ≤ Cl) (w : D.what₂.Word) (τ : D.what₂.Tau) :
    ShapeS (uS D w τ) (lamD D τ) (bOne D τ 1) := by
  have hI := std_interlace H w τ
  have hk := D.R.m_add_three_le_k
  have ha := (std_anti H τ).antitone
  intro s
  by_cases h : s.val < D.R.k - 1
  · exact ⟨fun _ => std_cloud_bd H hCl τ s h, fun hn => absurd (std_isCloud hI s (by omega)) hn⟩
  · refine ⟨fun hc => ?_, fun _ => std_node_bd H τ s h⟩
    exfalso
    obtain ⟨_, i, hi⟩ := hc
    have hil := i.isLt
    have h0 : lamD D τ s ≤ lamD D τ ⟨D.R.k - 1, by omega⟩ := ha (Fin.le_def.2 (by simp only; omega))
    by_cases h' : i.val + 1 < D.R.k
    · have h1 := (hI.1 i.val h').1
      have e : (⟨i.val, by omega⟩ : Fin D.R.k) = i := Fin.ext rfl
      rw [e] at h1
      have h2 : lamD D τ ⟨D.R.k - 1, by omega⟩ ≤ lamD D τ ⟨i.val, by omega⟩ :=
        ha (Fin.le_def.2 (by simp only; omega))
      linarith
    · have h1 := hI.2 (by omega)
      have e : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = i := Fin.ext (by simp only; omega)
      rw [e] at h1
      linarith

end Rec4

section Num

theorem std_num_nc (Cs Cl m n f L r3 : ℝ) (hm8 : 8 ≤ m) (hmn : m ≤ n) (hs : 128 * |Cs| ≤ m) (hCl : 8 ≤ Cl)
    (hf : 1 ≤ f) (hL : 1 ≤ L) (h30 : 0 ≤ r3) (h3 : r3 ≤ 2 * n) :
    Cs * m ^ ((9 : ℝ) / 2) * (r3 * n ^ 2 + n ^ 3) ≤ Cl * n ^ 19 * f ^ 5 * L := by
  have hCs0 := abs_nonneg Cs
  have hCs : Cs ≤ |Cs| := le_abs_self _
  have hn1 : 1 ≤ n := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hA0 : 0 ≤ m ^ ((9 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hA : m ^ ((9 : ℝ) / 2) ≤ n ^ 5 := by
    calc m ^ ((9 : ℝ) / 2) ≤ m ^ (5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m ^ 5 := by norm_cast
      _ ≤ n ^ 5 := pow_le_pow_left₀ (by linarith) hmn 5
  have hB0 : 0 ≤ r3 * n ^ 2 + n ^ 3 := by positivity
  have hB : r3 * n ^ 2 + n ^ 3 ≤ 3 * n ^ 3 := by
    have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ n ^ 2)
    have e : 2 * n * n ^ 2 = 2 * n ^ 3 := by ring
    linarith
  have hC : Cs ≤ n / 128 := by linarith
  have hC0 : (0 : ℝ) ≤ n / 128 := by positivity
  have s1 : Cs * m ^ ((9 : ℝ) / 2) ≤ n / 128 * n ^ 5 :=
    le_trans (mul_le_mul_of_nonneg_right hC hA0) (mul_le_mul_of_nonneg_left hA hC0)
  have s2 : Cs * m ^ ((9 : ℝ) / 2) * (r3 * n ^ 2 + n ^ 3) ≤ n / 128 * n ^ 5 * (3 * n ^ 3) :=
    le_trans (mul_le_mul_of_nonneg_right s1 hB0) (mul_le_mul_of_nonneg_left hB (by positivity))
  have s3 : n / 128 * n ^ 5 * (3 * n ^ 3) ≤ n ^ 9 := by
    have : (0 : ℝ) ≤ n ^ 9 := by positivity
    have e : n / 128 * n ^ 5 * (3 * n ^ 3) = 3 / 128 * n ^ 9 := by ring
    rw [e]; linarith
  have s4 : n ^ 9 ≤ n ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have a1 : n ^ 19 ≤ Cl * n ^ 19 := le_mul_of_one_le_left (by positivity) (by linarith)
  have a2 : Cl * n ^ 19 ≤ Cl * n ^ 19 * f ^ 5 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hf)
  have a3 : Cl * n ^ 19 * f ^ 5 ≤ Cl * n ^ 19 * f ^ 5 * L :=
    le_mul_of_one_le_right (by positivity) hL
  linarith

theorem std_num_bv (Cs m k n : ℝ) (hm8 : 8 ≤ m) (hmk : m ≤ k) (hs : 128 * |Cs| ≤ m) (hn0 : 0 ≤ n)
    (hn2k : n ≤ 2 * k) : Cs * n ^ 7 ≤ k ^ 8 := by
  have hCs0 := abs_nonneg Cs
  have hCs : Cs ≤ |Cs| := le_abs_self _
  have hk0 : 0 ≤ k := by linarith
  have h1 : n ^ 7 ≤ (2 * k) ^ 7 := pow_le_pow_left₀ hn0 hn2k 7
  have h2 : Cs * n ^ 7 ≤ |Cs| * (2 * k) ^ 7 :=
    le_trans (mul_le_mul_of_nonneg_right hCs (by positivity)) (mul_le_mul_of_nonneg_left h1 hCs0)
  have h3 : |Cs| * (2 * k) ^ 7 = 128 * |Cs| * k ^ 7 := by ring
  have h4 : 128 * |Cs| * k ^ 7 ≤ k * k ^ 7 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h5 : k * k ^ 7 = k ^ 8 := by ring
  linarith

theorem numerical_bound_first_alt (Cs Cl m k n : ℝ) (hm8 : 8 ≤ m) (hmk : m ≤ k) (hs : 128 * |Cs| ≤ m) (hCl : 8 ≤ Cl)
    (hn0 : 0 ≤ n) : Cs * m ^ 3 ≤ Cl * k * m ^ 4 + n * m ^ 10 := by
  have hCs0 := abs_nonneg Cs
  have hCs : Cs ≤ |Cs| := le_abs_self _
  have hm4 : m ^ 4 ≤ Cl * k * m ^ 4 := by
    have : (1 : ℝ) ≤ Cl * k := by nlinarith
    exact le_mul_of_one_le_left (by positivity) this
  have hn0' : 0 ≤ n * m ^ 10 := by positivity
  have h1 : Cs * m ^ 3 ≤ m * m ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : m * m ^ 3 = m ^ 4 := by ring
  linarith

theorem numerical_bound_second_alt (Cs' Cl m k n : ℝ) (hm8 : 8 ≤ m) (hmk : m ≤ k) (hs' : |Cs'| ≤ m) (hCl : 8 ≤ Cl)
    (hn0 : 0 ≤ n) : Cs' * k * m ^ 3 ≤ Cl * k * m ^ 4 + n * m ^ 10 := by
  have hCs' : Cs' ≤ |Cs'| := le_abs_self _
  have hn0' : 0 ≤ n * m ^ 10 := by positivity
  have h1 : Cs' * k * m ^ 3 ≤ m * k * m ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) (by positivity)
  have h2 : m * k * m ^ 3 = 1 * k * m ^ 4 := by ring
  have h3 : 1 * k * m ^ 4 ≤ Cl * k * m ^ 4 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) (by positivity)
  linarith

theorem std_num_position (Cs m k r De : ℝ) (hm8 : 8 ≤ m) (hk8 : 8 * m ^ 2 ≤ k) (hs : 128 * |Cs| ≤ m)
    (hr : 2 * r + 2 = m) (hDel : k ^ 2 ≤ De) :
    2 * (Cs * (r + 1) ^ 2) + 1 ≤ 3 * De ∧ 4 ≤ De ∧ Cs * (r + 1) ^ 2 ≤ De - 4 := by
  have hCs0 := abs_nonneg Cs
  have hCs : Cs ≤ |Cs| := le_abs_self _
  have hD64 : 64 * m ^ 4 ≤ De := by
    refine le_trans ?_ hDel
    have : (8 * m ^ 2) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (by positivity) hk8 2
    have e : (8 * m ^ 2) ^ 2 = 64 * m ^ 4 := by ring
    linarith
  have hm4' : (4096 : ℝ) ≤ m ^ 4 := by
    calc (4096 : ℝ) = 8 ^ 4 := by norm_num
      _ ≤ m ^ 4 := pow_le_pow_left₀ (by norm_num) hm8 4
  have hCr : Cs * (r + 1) ^ 2 ≤ m ^ 4 := by
    have e : r + 1 = m / 2 := by linarith
    rw [e]
    have h1 : Cs * (m / 2) ^ 2 ≤ m * (m / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : m * (m / 2) ^ 2 = m ^ 3 / 4 := by ring
    have h3 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : 0 ≤ m ^ 3 := by positivity
    linarith
  exact ⟨by linarith, by linarith, by linarith⟩

end Num

section Rec5

variable {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem std_position (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (w : D.what₂.Word) (τ : D.what₂.Tau) (X : ℝ)
    (hX : X ≤ 3 * (D.s.Del : ℝ)) : HasSeparatingGap (uS D w τ) (lamD D τ) X := by
  obtain ⟨_, d2, _⟩ := H.2.1
  have hI := std_interlace H w τ
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hD := std_Del_pos D
  have e1 : uS D w τ ⟨1, by omega⟩ = uOne D w τ (1 + 1) := std_uS D w τ ⟨1, by omega⟩
  have e2 : uS D w τ ⟨1 + 1, by omega⟩ = uOne D w τ (2 + 1) := std_uS D w τ ⟨1 + 1, by omega⟩
  have hv := vertex_difference_eq D τ
  refine ⟨1, by omega, ?_, ⟨⟨0, by omega⟩, std_isCloud hI _ (by simp only; omega), (hI.1 0 (by omega)).2.le⟩,
    ⟨⟨2, by omega⟩, std_isCloud hI _ (by simp only; omega), (hI.1 2 (by omega)).1.le⟩⟩
  rw [e1, e2]
  rcases d2 w 1 le_rfl (by omega) with a | a <;> rcases d2 w 2 (by omega) (by omega) with b | b <;>
    rw [a τ, b τ] <;> linarith

theorem std_cutW (H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (w w' : D.what₂.Word) (τ : D.what₂.Tau) (X : ℝ)
    (hne : uS D w τ ≠ uS D w' τ) (hD4 : 4 ≤ (D.s.Del : ℝ)) (hX : X ≤ (D.s.Del : ℝ) - 4) :
    HasCut (uS D w τ) (uS D w' τ) X := by
  obtain ⟨_, d2, _⟩ := H.2.1
  have hk := D.R.m_add_three_le_k
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hil := i.isLt
  have h0 : i.val ≠ 0 := by
    intro h
    apply hi
    have e : i = ⟨0, by omega⟩ := Fin.ext h
    unfold uS
    rw [e, D.hcW_first w τ (by omega), D.hcW_first w' τ (by omega)]
  have h1 : i.val ≠ D.R.k - 1 := by
    intro h
    apply hi
    have e : i = ⟨D.R.k - 1, by omega⟩ := Fin.ext h
    unfold uS
    rw [e, D.hcW_last w τ (by omega), D.hcW_last w' τ (by omega)]
  have ei : i.val - 1 + 1 + 1 = i.val + 1 := by omega
  have a := d2 w (i.val - 1 + 1) (by omega) (by omega)
  have b := d2 w' (i.val - 1 + 1) (by omega) (by omega)
  rw [ei] at a b
  rw [std_uS, std_uS] at hi
  refine ⟨_, _, std_cut (uS D w τ) (uS D w' τ) i (vOne D τ (i.val - 1 + 1) - 1 / 2) (D.s.Del : ℝ) ?_ hD4, by linarith⟩
  rw [std_uS, std_uS]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd (by rw [a τ, b τ]) hi
  · exact Or.inl ⟨a τ, b τ⟩
  · exact Or.inr ⟨a τ, b τ⟩
  · exact absurd (by rw [a τ, b τ]) hi

theorem stdOfHyp_rec (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ : ℝ)
    (hCl : 8 ≤ Cl) (hCh : 0 ≤ Ch) (hβ : 2 ≤ Cβ) (hu : Cu ≤ Cβ) (hT : CT ≤ Cβ * Ch)
    (hg : 1 / 8 + 2 * Cg ≤ Cβ * Ch) (hs : 128 * |Cs| ≤ D.R.m) (hs' : |Cs'| ≤ D.R.m) :
    StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ := by
  intro H τ w w'
  obtain ⟨hm8, hmk, hk8, hDel, hf⟩ := std_sizes H hCl
  obtain ⟨hka0, hka1, hka2⟩ := std_kaS H hCl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _, _⟩ := H.1
  have hb := std_b_gt D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hL := std_L_ge D large₂
  have hn := std_r_add D
  have hrS : 2 * (D.R.rS : ℝ) + 2 = D.R.m := by have := std_castM D; push_cast at this; exact this
  have hpw : ∀ y : ℝ, (large₂.sc.b ^ Cβ) ^ y = large₂.sc.b ^ (Cβ * y) := fun y => (Real.rpow_mul hb0.le Cβ y).symm
  have hb2 : large₂.sc.b ^ (2 : ℝ) ≤ large₂.sc.b ^ Cβ := Real.rpow_le_rpow_of_exponent_le hb.le hβ
  have hbu : large₂.sc.b ^ Cu ≤ large₂.sc.b ^ Cβ := Real.rpow_le_rpow_of_exponent_le hb.le hu
  have hT1 : ∀ w : D.what₂.Word, 1 ≤ Tr D w := fun w => by
    have := (D.mem w).A.T_prime.one_lt
    unfold Tr
    exact_mod_cast this.le
  have hT2 : ∀ w : D.what₂.Word, Tr D w ≤ (large₂.sc.b ^ Cβ) ^ (Ch * ((2 * D.R.rS + 2 : ℕ) : ℝ)) := fun w => by
    rw [hpw, std_castM]
    refine le_trans (h23 w).2 (Real.rpow_le_rpow_of_exponent_le hb.le ?_)
    have := mul_le_mul_of_nonneg_right hT (by linarith : (0 : ℝ) ≤ D.R.m)
    linarith
  have hn0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hG1 : Cs * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 ≤
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by
    rw [std_castM]; exact numerical_bound_first_alt _ _ _ _ _ hm8 hmk hs hCl hn0
  have hG2 : Cs' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 ≤
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by
    rw [std_castM]; exact numerical_bound_second_alt _ _ _ _ _ hm8 hmk hs' hCl hn0
  have hNC : Cs * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) ≤
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    rw [std_castM, std_castN]
    exact std_num_nc _ _ _ _ _ _ _ hm8 (by linarith) hs hCl hf hL (by positivity) (by push_cast; linarith)
  have hbv : Cs * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bOne D τ 1 := by
    rw [std_castN]
    exact le_trans (std_num_bv _ _ _ _ hm8 hmk hs hn0 (by linarith)) (first_node_size_bounds H hCl τ).1
  obtain ⟨hS1, hS2, hS3⟩ := std_num_position Cs _ _ _ _ hm8 hk8 hs hrS hDel
  refine ⟨⟨std_isHC H τ, std_interlace H w τ, std_interlace H w' τ, hka0, ?_, ?_, hT1 w, hT1 w', hT2 w, hT2 w',
    fun s => le_trans (std_lam_abs H hCl τ s) hb2,
    fun i => le_trans (std_u_abs H hCl w τ i) (max_le hb2 hbu),
    fun i => le_trans (std_u_abs H hCl w' τ i) (max_le hb2 hbu),
    std_allGaps H τ _ hG1, fun a b he => le_trans hNC (std_ncgap H τ a b he),
    ⟨bOne D τ 1, hbv, std_shape H hCl w τ⟩, ?_⟩, std_allGaps H τ _ hG2⟩
  · exact le_trans hka1 (Real.one_le_rpow (Real.one_le_rpow hb.le (by linarith)) hCh)
  · rw [hpw]
    exact le_trans hka2 (Real.rpow_le_rpow_of_exponent_le hb.le hg)
  · by_cases he : uS D w τ = uS D w' τ
    · exact Or.inl ⟨he, std_position H w τ _ hS1⟩
    · exact Or.inr ⟨he, std_cutW H w w' τ _ he hS2 hS3⟩

end Rec5

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem stdHypS_of (Cg cb Cu cT CT C0 Ch Cβ : ℝ) (hCl : 8 ≤ sCl Fm) (hCh : 0 ≤ Ch) (hβ : 2 ≤ Cβ) (hu : Cu ≤ Cβ)
    (hT : CT ≤ Cβ * Ch) (hg : 1 / 8 + 2 * Cg ≤ Cβ * Ch) : PX.StdHypS Fm Cg cb Cu cT CT C0 Ch Cβ := by
  intro Cs Cs'
  obtain ⟨x0, _, h0⟩ := ev_m Fm (max (128 * |Cs|) |Cs'|)
  exact ownEv_intro Fm x0 (fun x hx _ i => stdOfHyp_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCl hCh hβ hu hT hg
    (le_trans (le_max_left _ _) (h0 x hx i)) (le_trans (le_max_right _ _) (h0 x hx i)))

end Fam

end Formalism.MainNotions.BridgeLemma

end
