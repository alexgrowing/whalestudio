import Formalism.SharpRestriction.InertJacobiLevels.TiesLat

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Num

variable {D : D7}

def xG (D : D7) (τ : D.what₂.Tau) (j : ℕ) : ℝ := wj D (min j D.R.m) τ - G.kaJ D (min j D.R.m)

def wZof (D : D7) (τ : D.what₂.Tau) (j : ℕ) : ℤ := ⌊xG D τ j⌋

theorem wj_eq (τ : D.what₂.Tau) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    wj D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold wj
  rw [dif_pos (by omega)]

theorem kaJ_int (D : D7) (j : ℕ) (_h1 : 1 ≤ j) : ∃ z : ℤ, G.kaJ D j = z := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.t_odd
  refine ⟨(a : ℤ) + (2 * (j : ℤ) - 1) * ((b : ℤ) + 1), ?_⟩
  unfold G.kaJ
  rw [ha, hb]
  push_cast
  ring

theorem wZof_eq (τ : D.what₂.Tau) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    ((wZof D τ j : ℤ) : ℝ) = wj D j τ - G.kaJ D j := by
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨z, hz⟩ := (D.hc τ).e_int ⟨j - 1, by omega⟩
  obtain ⟨y, hy⟩ := kaJ_int D j hj'.1
  have e : xG D τ j = ((z - y : ℤ) : ℝ) := by
    unfold xG
    rw [min_eq_left hj'.2, wj_eq τ j hj'.1 hj'.2, hz, hy]
    push_cast
    ring
  unfold wZof
  rw [e, Int.floor_intCast, ← e]
  unfold xG
  rw [min_eq_left hj'.2]

theorem xG_mono (τ : D.what₂.Tau) (j : ℕ) (h1 : 1 ≤ j) : xG D τ j ≤ xG D τ (j + 1) := by
  unfold xG
  by_cases h : j + 1 ≤ D.R.m
  · rw [min_eq_left h, min_eq_left (by omega : j ≤ D.R.m), wj_eq τ j h1 (by omega), wj_eq τ (j + 1) (by omega) h]
    have g1 := (D.hc τ).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < D.R.m; omega)
    have g2 := (D.hc τ).gap_be ⟨j, by omega⟩
    have e1 : (⟨(⟨j - 1, by omega⟩ : Fin D.R.m).1 + 1, by show j - 1 + 1 < D.R.m; omega⟩ : Fin D.R.m) =
        ⟨j, by omega⟩ := Fin.ext (by show j - 1 + 1 = j; omega)
    rw [e1] at g1
    have e2 : (⟨j + 1 - 1, by omega⟩ : Fin D.R.m) = ⟨j, by omega⟩ := Fin.ext (by show j + 1 - 1 = j; omega)
    rw [e2]
    have g1' : (((D.R.t : ℚ) + 3) / 2 : ℚ) + (((D.R.t : ℚ) + 3) / 2 : ℚ) ≤
        (D.hc τ).e ⟨j, by omega⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ := by linarith
    have g3 : (((((D.R.t : ℚ) + 3) / 2 : ℚ) + (((D.R.t : ℚ) + 3) / 2 : ℚ) : ℚ) : ℝ) ≤
        (((D.hc τ).e ⟨j, by omega⟩ - (D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast g1'
    push_cast at g3
    unfold G.kaJ
    push_cast
    linarith
  · rw [min_eq_right (by omega : D.R.m ≤ j + 1), min_eq_right (by omega : D.R.m ≤ j)]

theorem wZof_mono (τ : D.what₂.Tau) (j : ℕ) (h1 : 1 ≤ j) : wZof D τ j ≤ wZof D τ (j + 1) :=
  Int.floor_le_floor (xG_mono τ j h1)

theorem xG_one (τ : D.what₂.Tau) : xG D τ 1 = wj D 1 τ - G.kaJ D 1 := by
  unfold xG
  rw [min_eq_left (by have := D.R.two_le_m; omega)]

variable (hT : GatTies D)

theorem lambda_real_eq_shifted_weight (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV)
    (s : Fin ((D.gat u w hg).P.n' v)) (i : Fin ((D.gat u w hg).P.m + 1)) (hi : i.1 < D.R.k) :
    (((D.gat u w hg).P.lam0 v s i : ℤ) : ℝ) =
      (((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨i.1, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ)) := by
  rw [hT.gat_lam u w hg v s i]
  have h := (D.fm u).lam_eq 0 (Nat.zero_le _) (hT.gat_pos u w hg ⟨v, s⟩)
    ⟨i.1, by simp only [Ranks.N]; omega⟩
  rw [dif_pos hi] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [hcToWeightQ, rhoVec] at h'
  push_cast at h'
  exact h'

end Num

section Build

variable {D : D7} (hT : GatTies D) (L : SizeData₂ D)

theorem base_top_of (c : ℕ) (hcl : L.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV)
    (s : Fin ((D.gat u w hg).P.n' v)) (t : D.host.TT)
    (ht : ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 t) :
    (D.gat u w hg).P.lam0 v s 0 = L.aT t ∧ (D.gat u w hg).P.lam0 v s (Fin.last _) = -L.bT t ∧
      ∀ i : Fin ((D.gat u w hg).P.m + 1), 0 < i.val → i.val < (D.gat u w hg).P.m →
        |(D.gat u w hg).P.lam0 v s i| ≤ c := by
  have hk := hT.gat_k u w hg
  have hk0 : 0 < D.R.k := by omega
  have hkR : (((D.gat u w hg).P.m : ℕ) : ℝ) + 1 = (D.R.k : ℝ) := by exact_mod_cast hk
  have tu := L.top_u (hT.gat_pos u w hg ⟨v, s⟩) t hk0 ht
  refine ⟨?_, ?_, ?_⟩
  · have h := lambda_real_eq_shifted_weight hT u w hg v s 0 (by simpa using hk0)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(0 : Fin ((D.gat u w hg).P.m + 1)).1, by simpa using hk0⟩ : Fin D.R.k) = ⟨0, hk0⟩ :=
      Fin.ext (by simp)
    rw [e, D.hcW_first u _ hk0, tu.1]
    simp
  · have h := lambda_real_eq_shifted_weight hT u w hg v s (Fin.last _) (by simp only [Fin.val_last]; omega)
    apply Int.cast_injective (α := ℝ)
    rw [h]
    have e : (⟨(Fin.last (D.gat u w hg).P.m).1, by simp only [Fin.val_last]; omega⟩ : Fin D.R.k) =
        ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [e, D.hcW_last u _ hk0, tu.2]
    simp only [Fin.val_last]
    push_cast
    linarith
  · intro i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := lambda_real_eq_shifted_weight hT u w hg v s i hi
    have cl := L.cloud_u u (hT.gat_pos u w hg ⟨v, s⟩) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have hS := L.Sc_pos
    have h2 : |(((D.gat u w hg).P.lam0 v s i : ℤ) : ℝ)| ≤ (c : ℝ) := by
      rw [h, abs_le]
      constructor <;> linarith [cl.1, cl.2]
    exact_mod_cast h2

theorem base_off_of (c : ℕ)
    (hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
      |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV)
    (s : Fin ((D.gat u w hg).P.n' v))
    (hn : ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces)
    (i : Fin ((D.gat u w hg).P.m + 1)) : |(D.gat u w hg).P.lam0 v s i| ≤ c := by
  have hk := hT.gat_k u w hg
  have hi : i.1 < D.R.k := by omega
  have h := lambda_real_eq_shifted_weight hT u w hg v s i hi
  have h2 := hoff u _ hn ⟨i.1, hi⟩
  rw [← h] at h2
  exact_mod_cast h2

theorem bT_le_xG (τ : D.what₂.Tau) (t : D.host.TT) (ht : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    (L.bT t : ℝ) ≤ xG D τ 1 := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have tb := L.top_b τ t hm ht
  have g := (D.hc τ).gap_be ⟨0, hm⟩
  have g' : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e ⟨0, hm⟩ - (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
    exact_mod_cast g
  push_cast at g'
  rw [xG_one, wj_eq τ 1 le_rfl (by omega)]
  have e : (⟨1 - 1, by omega⟩ : Fin D.R.m) = ⟨0, hm⟩ := rfl
  rw [e]
  unfold G.kaJ
  push_cast
  linarith

variable {L} (X : G.Inst D L)

structure PosHyp where
  vOf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    G.HH D → Fin (D.gat u w hg).P.nV
  inj : ∀ u w hg, Set.InjOn (vOf u w hg) (G.reps X (D.what₂.places.resChar w))
  n_eq : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w),
    (D.gat u w hg).P.n' (vOf u w hg t0) = addOrderOf (G.hP D (D.what₂.places.resChar w))
  pos : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w), ∀ s : Fin ((D.gat u w hg).P.n' (vOf u w hg t0)),
    ((D.eTau (hT.gat_pos u w hg ⟨vOf u w hg t0, s⟩) : D.R.Psi) : D.R.GG) =
      D.R.tau1 (t0 + s.val • G.hP D (D.what₂.places.resChar w))
  r_eq : ∀ u w hg, (D.gat u w hg).P.r =
    (if ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k then G.rG L.sc else 1)

def latHypOf (P : PosHyp hT X) (c : ℕ) (c_le : (c : ℝ) ≤ G.cG L) (hcl : L.Sc + ((D.R.k : ℝ) - 1) / 2 ≤ c)
    (hoff : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
      |(((D.hcW u τ).u i : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c)
    (hw1 : ∀ τ, (c : ℝ) ≤ wj D 1 τ - G.kaJ D 1) : LatHyp hT X where
  vOf := P.vOf
  inj := P.inj
  n_eq := P.n_eq
  pos := P.pos
  r_eq := P.r_eq
  c := c
  c_le := c_le
  wZ := wZof D
  wZ_eq := wZof_eq
  wZ_mono := wZof_mono
  base_top := base_top_of hT L c hcl
  base_off := base_off_of hT c hoff
  wZ_ge := fun u w hg v s => by
    have hc : (c : ℤ) ≤ wZof D (hT.gat_pos u w hg ⟨v, s⟩) 1 := by
      refine Int.le_floor.2 ?_
      rw [xG_one]
      push_cast
      exact hw1 _
    refine max_le hc ?_
    by_cases htop : ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      rw [(base_top_of hT L c hcl u w hg v s ⟨t, ht⟩ hte.symm).2.1, neg_neg]
      exact Int.le_floor.2 (bT_le_xG L _ ⟨t, ht⟩ hte.symm)
    · exact ((neg_le_abs _).trans (base_off_of hT c hoff u w hg v s htop _)).trans hc

end Build

end Formalism.MainNotions.Inhab

end
