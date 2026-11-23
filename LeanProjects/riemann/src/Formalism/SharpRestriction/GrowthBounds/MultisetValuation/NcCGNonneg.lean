import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LambdaIndexTwo

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_m_ge (hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : 2 ≤ (D.gat u w hg).P.m := by
  have h1 := hT.gat_k u w hg
  have h2 := D.R.m_add_three_le_k
  omega

theorem nc_cG_nonneg : 0 ≤ Formalism.MainNotions.G.cG L := by
  unfold Formalism.MainNotions.G.cG
  have h := L.Sc_pos
  linarith

private theorem liftWt_apply_of_lt_succ (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j i : ℕ)
    (hi : i < m + j * (t + 1) + 1) (h : i < m + 1) :
    Formalism.MainNotions.G.liftWt t m lam w j ⟨i, hi⟩ = lam ⟨i, h⟩ :=
  dif_pos h

private theorem lam_antitone_of_isDominant_liftWt {n' m : ℕ} (t : ℕ) (lam : Fin n' → Fin (m + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (hd : Formalism.MainNotions.G.IsDominant fun s => Formalism.MainNotions.G.liftWt t m (lam s) (fun i => w i s) 0)
    (s : Fin n') (i i' : ℕ) (hi : i < m + 1) (hi' : i' < m + 1) (hii : i ≤ i') :
    lam s ⟨i', hi'⟩ ≤ lam s ⟨i, hi⟩ := by
  unfold Formalism.MainNotions.G.IsDominant at hd
  have h1 := hd s (show (⟨i, by omega⟩ : Fin (m + 0 * (t + 1) + 1)) ≤ ⟨i', by omega⟩ from
    Fin.mk_le_mk.mpr hii)
  calc lam s ⟨i', hi'⟩ = Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i', by omega⟩ :=
        (liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i' (by omega) hi').symm
    _ ≤ Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i, by omega⟩ := h1
    _ = lam s ⟨i, hi⟩ := liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i (by omega) hi

private theorem lamI_one_eq_lam0_zero {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 = lam0 s ⟨0, by omega⟩ :=
  dif_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem lamI_two_eq_lam0_one {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n')
    (hk : 1 ≤ k1) : Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 = lam0 s ⟨1, by omega⟩ :=
  dif_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem nu_one_eq_lamI_one_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 1 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 + w j s :=
  if_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem nu_two_eq_lamI_two_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') (hk : 1 ≤ k1) :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 2 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 + w j s :=
  if_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem le_of_monotone_from_one (f : ℕ → ℤ) (h : ∀ j, 1 ≤ j → f j ≤ f (j + 1)) :
    ∀ j, 1 ≤ j → f 1 ≤ f j := by
  intro j hj
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      subst hn0
      exact le_refl _
    · exact (ih hn).trans (h n hn)

private theorem le_and_neg_le_of_abs_le_of_le (x : ℤ) (c : ℕ) (g : ℝ) (hx : |x| ≤ (c : ℤ)) (hc : (c : ℝ) ≤ g) :
    (x : ℝ) ≤ g ∧ -(x : ℝ) ≤ g := by
  have h := abs_le.mp hx
  have h1 : (x : ℝ) ≤ (c : ℝ) := by exact_mod_cast h.2
  have h2 : -(c : ℝ) ≤ (x : ℝ) := by exact_mod_cast h.1
  constructor <;> linarith

theorem nc_ties (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    let v := Y.vOf u w hg t0
    let Fl := Y.Fl u w hg
    (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
    (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) := by
  dsimp only
  unfold Formalism.MainNotions.G.LatTied at hL
  have hm : 2 ≤ (D.gat u w hg).P.m := nc_m_ge hT u w hg
  have hm1 : 1 ≤ (D.gat u w hg).P.m := by omega
  have hcG : (0 : ℝ) ≤ Formalism.MainNotions.G.cG L := nc_cG_nonneg
  obtain ⟨-, -, hc, -, -, -, hrep⟩ := hL u w hg
  obtain ⟨-, hs⟩ := hrep t0 ht0
  have hbase := (Y.Fl u w hg).base (Y.vOf u w hg t0)
  unfold Formalism.MainNotions.G.IsBaseWeight at hbase
  have hd := (Y.Fl u w hg).domJ 0 (Y.vOf u w hg t0)
  have hwge := (Y.Fl u w hg).w_ge (Y.vOf u w hg t0)
  have hwm := (Y.Fl u w hg).w_mono (Y.vOf u w hg t0)
  have h0 : 0 < (D.gat u w hg).P.m + 1 := by omega
  have h1 : 1 < (D.gat u w hg).P.m + 1 := by omega
  have hM : (D.gat u w hg).P.m < (D.gat u w hg).P.m + 1 := by omega
  have e0 : (0 : Fin ((D.gat u w hg).P.m + 1)) = ⟨0, h0⟩ := Fin.ext (by simp)
  have hA01 : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 0 1 h0 h1 (by omega)
  have hA1M : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 1 (D.gat u w hg).P.m h1 hM (by omega)
  have hTT1 : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩| ≤ ((Y.Fl u w hg).c : ℤ) :=
    fun s hsT => ((hbase s).1 hsT).2.2 ⟨1, h1⟩ Nat.one_pos (show 1 < (D.gat u w hg).P.m by omega)
  have hA : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ = (Y.Fl u w hg).a (Y.vOf u w hg t0) s := by
    intro s hsT
    rw [← e0]
    exact ((hbase s).1 hsT).1
  have hN0 : ∀ s, s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩| ≤ ((Y.Fl u w hg).c : ℤ) := by
    intro s hsT
    rw [← e0]
    exact (hbase s).2 hsT 0
  have hwZ : ∀ s, -(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s := fun s => (le_max_right _ _).trans (hwge s)
  have hwj : ∀ s j, 1 ≤ j →
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s ≤ (Y.Fl u w hg).w (Y.vOf u w hg t0) j s :=
    fun s => le_of_monotone_from_one (fun j => (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) (fun j hj => hwm s j hj)
  have hj1 : 1 ≤ j := by
    unfold Formalism.BasicNotions.SizeData₂.lifts at hj
    exact (Finset.mem_Icc.mp hj).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hsT
    have hA' := (hA s hsT).trans ((hs s).2.2.1 hsT).1
    have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_ya Formalism.MainNotions.G.al Formalism.MainNotions.FormalGroupSystem.al
    simp only [hsT, ↓reduceIte]
    rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1, hA']
    push_cast
    linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.al
    split_ifs with hsT
    · rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA01 s]
    · exact le_refl 0
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_zc Formalism.MainNotions.FormalGroupSystem.cap
    rw [← (hs s).2.2.2 j hj]
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
      push_cast
      linarith
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hN0 s hsT) hc).1
      push_cast
      linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.cap
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA1M s, hwZ s, hwj s j hj1]
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      linarith [hA01 s, hA1M s, hwZ s, hwj s j hj1]

end Formalism.MainNotions.FormalGroupSystem.Pf
