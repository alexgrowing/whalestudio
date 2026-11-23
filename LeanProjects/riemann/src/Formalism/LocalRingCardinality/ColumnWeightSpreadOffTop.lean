import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataGatTies
import Formalism.SharpRestriction.GrowthBounds.ObjPol

open Formalism.MainNotions.G Formalism.FrobeniusOrbits

noncomputable section

namespace Formalism.BasicNotions

namespace Scale

variable (s : Scale)

theorem x_pos : 0 < s.x := lt_trans one_pos s.one_lt_alt

theorem a_pos : 0 < s.a := mul_pos s.x_pos (Real.exp_pos _)

theorem one_le_X' : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg s.x_pos.le _)

theorem b'_pos : 0 < s.b' := div_pos s.a_pos (lt_of_lt_of_le one_pos s.one_le_X')

theorem b'_le_a : s.b' ≤ s.a := div_le_self s.a_pos.le s.one_le_X'

theorem w''_le_b' (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1 : ℝ) ≤ s.x * n := by nlinarith [s.one_lt_alt]
  exact div_le_self s.b'_pos.le h2

theorem w''_le_a (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.a := (s.w''_le_b' n hn).trans s.b'_le_a

end Scale

theorem Ranks.one_le_n (R : Ranks) : 1 ≤ R.n := R.ord_pos

theorem Ranks.five_le_k (R : Ranks) : 5 ≤ R.k := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  omega

namespace ParameterChoice'

variable {D : D7} {L : SizeData₂ D}

theorem five_le_k (_P : ParameterChoice' D L) : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.five_le_k

theorem LaG_pos (P : ParameterChoice' D L) : 0 < L.LaG := by
  have hk : (0 : ℝ) < D.R.k := by linarith [P.five_le_k]
  have h1 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith [P.S_le, L.Sc_pos]
  have h2 : 0 < L.LaG * L.sc.b' := by
    have := mul_pos h1 hk
    rwa [div_mul_cancel₀ _ hk.ne'] at this
  exact (pos_iff_pos_of_mul_pos h2).mpr L.sc.b'_pos

theorem Sc_ge (P : ParameterChoice' D L) : 4096 * (D.R.k : ℝ) ^ 2 ≤ L.Sc := by
  have hk := P.five_le_k
  have hD := P.Del_ge.2.2.2
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hm10 : (1024 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    calc (1024 : ℝ) = 2 ^ 10 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hm 10
  have hN : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have h1 : (D.R.k : ℝ) * 1024 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
    mul_le_mul hN hm10 (by norm_num) (by linarith)
  rw [L.Sc_eq]
  nlinarith

theorem kSc_le_a (P : ParameterChoice' D L) : (D.R.k : ℝ) * L.Sc ≤ L.sc.a :=
  P.kS_le.trans (L.sc.w''_le_a _ D.R.one_le_n)

theorem Sc_le (P : ParameterChoice' D L) : 5 * L.Sc ≤ L.sc.a := by
  have := P.kSc_le_a
  nlinarith [P.five_le_k, L.Sc_pos]

theorem k_le_a (P : ParameterChoice' D L) : (D.R.k : ℝ) ≤ L.sc.a := by
  have h1 := P.kSc_le_a
  have h2 := P.Sc_ge
  have h3 := P.five_le_k
  nlinarith

theorem four_le_a (P : ParameterChoice' D L) : 4 ≤ L.sc.a := by linarith [P.k_le_a, P.five_le_k]

theorem bT_le' (P : ParameterChoice' D L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hk : (0 : ℝ) < D.R.k := by linarith [P.five_le_k]
  have hx := L.sc.one_lt_alt
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le hlog.le) P.LaG_pos.le) hk.le
  have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h4 := P.rho_le
  unfold LevelStarExponents.rhoP at h4
  have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
      4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h7 := P.bT_le t
  rw [h6] at h7
  nlinarith [L.sc.b'_pos]

end ParameterChoice'

theorem SizeData₂.aT_le' {D : D7} (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 6 / 5 * L.sc.a := by
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.five_le_k
  have hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have h1 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left L.sc.a_pos.le (by norm_num) h5
  linarith [(L.aT_win t).2]

section Spread

variable {D : D7}

def lamFst (D : D7) : Fin (D.R.N 0) := ⟨0, by have := D.R.five_le_k; simp only [Ranks.N]; omega⟩

def lamLst (D : D7) : Fin (D.R.N 0) := ⟨D.R.k - 1, by have := D.R.five_le_k; simp only [Ranks.N]; omega⟩

theorem columnWeight_spread_eq (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) =
      (((D.hc τ).u ⟨0, by have := D.R.five_le_k; omega⟩ : ℚ) : ℝ) -
        (((D.hc τ).u ⟨D.R.k - 1, by have := D.R.five_le_k; omega⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) - 1) := by
  have hk := D.R.five_le_k
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (lamFst D)
  have h1 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (lamLst D)
  have c0 : (lamFst D).1 < D.R.k := by simp only [lamFst]; omega
  have c1 : (lamLst D).1 < D.R.k := by simp only [lamLst]; omega
  rw [dif_pos c0] at h0
  rw [dif_pos c1] at h1
  simp only [hcToWeightQ, rhoVec, lamFst, lamLst] at h0 h1
  rw [D.hcW_first u τ (by omega)] at h0
  rw [D.hcW_last u τ (by omega)] at h1
  have hc : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at h1
  have hq : ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℚ) =
      (D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).u ⟨D.R.k - 1, by omega⟩ - ((D.R.k : ℚ) - 1) := by
    push_cast
    simp only [lamFst, lamLst]
    rw [h0, h1]
    push_cast
    ring
  have := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at this ⊢
  linarith

theorem columnWeight_spread_nonneg (u : D.what₂.Word) (τ : D.what₂.Tau) :
    0 ≤ ((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) := by
  have := ((D.fm u).lam 0 τ).anti (show lamFst D ≤ lamLst D from Nat.zero_le _)
  omega

variable {L : SizeData₂ D}

theorem columnWeight_spread_at_top (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (t : D.host.TT)
    (ht : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    ((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) = L.aT t + L.bT t := by
  have h := columnWeight_spread_eq u τ
  obtain ⟨h1, h2⟩ := L.top_u τ t (by have := D.R.five_le_k; omega) ht
  rw [h1, h2] at h
  have : ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) = ((L.aT t + L.bT t : ℤ) : ℝ) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

theorem columnWeight_spread_off_top (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (ht : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) ≤ 3 * L.Sc := by
  have hk := D.R.five_le_k
  have hkR := P.five_le_k
  rw [columnWeight_spread_eq u τ]
  have h1 := P.cloud_place_bound τ (by omega) ht
  have h2 := P.uk_extreme τ (by omega) ht
  have h3 := (L.cloud_v τ ⟨0, by omega⟩).2
  have h4 := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
  rw [h2]
  push_cast at h1 ⊢
  linarith

theorem columnWeight_spread_le (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).w (lamFst D) - ((D.fm u).lam 0 τ).w (lamLst D) : ℤ) : ℝ) ≤ 3 * L.sc.a := by
  by_cases ht : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htT, hte⟩ := Finset.mem_image.mp ht
    rw [columnWeight_spread_at_top L u τ ⟨t, htT⟩ hte.symm]
    have h1 := L.aT_le' ⟨t, htT⟩
    have h2 := P.bT_le' ⟨t, htT⟩
    have h3 := L.sc.b'_le_a
    push_cast
    linarith [L.sc.a_pos]
  · have h1 := columnWeight_spread_off_top P u τ ht
    have h2 := P.Sc_le
    linarith [L.Sc_pos]

theorem gat_ell_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) : ℤ) : ℝ) ≤ 3 * L.sc.a := by
  have hk := T.gat_k u w h
  rw [T.gat_lam u w h v s 0, T.gat_lam u w h v s (Fin.last _)]
  have e0 : (⟨(0 : Fin ((D.gat u w h).P.m + 1)).1, by
      have h1 := T.gat_k u w h; simp only [Ranks.N]; simp; omega⟩ : Fin (D.R.N 0)) = lamFst D := rfl
  have e1 : (⟨(Fin.last (D.gat u w h).P.m).1, by
      have h1 := T.gat_k u w h; simp only [Ranks.N]; simp; omega⟩ : Fin (D.R.N 0)) = lamLst D := by
    apply Fin.ext
    simp only [lamLst, Fin.val_last]
    omega
  rw [e0, e1]
  exact columnWeight_spread_le P u _

theorem gat_ellWt_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (ellWt ((D.gat u w h).P.lam0 v s) : ℝ) ≤ 3 * L.sc.a := by
  have h1 := gat_ell_le P T u w h v s
  have h2 : 0 ≤ (D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) := by
    have := (D.gat u w h).P.dom v s (Fin.zero_le (Fin.last _))
    omega
  have h3 : lastIdx ((D.gat u w h).P.m + 1) = Fin.last _ := rfl
  unfold ellWt
  rw [h3]
  have h4 : ((((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _)).toNat : ℕ) : ℝ) =
      (((D.gat u w h).P.lam0 v s 0 - (D.gat u w h).P.lam0 v s (Fin.last _) : ℤ) : ℝ) := by
    have := Int.toNat_of_nonneg h2
    exact_mod_cast this
  rw [h4]
  exact h1

theorem ellWt_lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    ellWt (lamAt lam0 s) = ellWt (lam0 s) := by
  have h3 : lastIdx (m + 1) = Fin.last _ := rfl
  unfold ellWt lamAt
  rw [h3]
  split_ifs
  · rfl
  · simp only [Fin.rev_zero, Fin.rev_last]
    congr 1
    ring

theorem gat_ellWt_lamAt_le (P : ParameterChoice' D L) (T : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w h).P.nV)
    (s : Fin ((D.gat u w h).P.n' v)) :
    (ellWt (lamAt ((D.gat u w h).P.lam0 v) s) : ℝ) ≤ 3 * L.sc.a := by
  rw [ellWt_lamAt]
  exact gat_ellWt_le P T u w h v s

end Spread

end Formalism.BasicNotions

end
