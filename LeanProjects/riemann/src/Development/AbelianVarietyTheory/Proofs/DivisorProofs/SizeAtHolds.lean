import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SizeProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sizes

variable {D : D7} {L : SizeData₂ D}

theorem cloudLen_le (L : SizeData₂ D) : (cloudLen D : ℝ) ≤ L.Sc := by
  have key : ∀ τ i, 0 ≤ (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i ∧
      (((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i : ℤ) : ℝ) ≤ L.Sc := fun τ i => by
    dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v τ ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc τ).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc τ).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  have h0 := L.Sc_pos.le
  have hL : cloudLen D ≤ ⌊L.Sc⌋₊ := by
    unfold cloudLen
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := key τ 2
    obtain ⟨b0, -⟩ := key τ D.R.k
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 = u at *
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k = v at *
    have h : ((u - v).toNat : ℤ) ≤ u := by omega
    have h' : (((u - v).toNat : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (cloudLen D : ℝ) ≤ (⌊L.Sc⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ L.Sc := Nat.floor_le h0

theorem gap_le (D : D7) (B : ℝ) (hB : 1 ≤ B) (hc : Real.sqrt (cloudLen D) ≤ B) (hm : 44 ≤ D.R.m) :
    (gap D 1 : ℝ) ≤ 4 * (D.R.t : ℝ) ^ 7 * B := by
  have h1 := D.R.rank_add_five_le
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.m_add_three_le_k
  have hr : D.R.r + 5 ≤ D.R.t := h1
  have hk : D.R.k ≤ D.R.t := by omega
  set t := D.R.t with ht
  have hN : bigN D ≤ 5 * t ^ 2 := by
    unfold bigN sLen
    have : D.R.m * (t + (D.R.r + 6) + 1) ≤ t * (3 * t) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hn : nRk D ≤ t := by unfold nRk; omega
  have hs : sLen D ≤ 2 * t := by unfold sLen; omega
  have t1 : (132 : ℝ) ≤ t := by exact_mod_cast (by omega : 132 ≤ t)
  have hN' : (bigN D : ℝ) ≤ 5 * (t : ℝ) ^ 2 := by exact_mod_cast hN
  have hn' : (nRk D : ℝ) ≤ t := by exact_mod_cast hn
  have hs' : (sLen D : ℝ) ≤ 2 * t := by exact_mod_cast hs
  have hm' : (D.R.m : ℝ) ≤ t := by exact_mod_cast (by omega : D.R.m ≤ t)
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have a1 : (bigN D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc (bigN D : ℝ) ^ 3 ≤ (5 * (t : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hN' 3
      _ = 125 * (t : ℝ) ^ 6 := by ring
      _ ≤ t * (t : ℝ) ^ 6 := by gcongr; linarith
      _ = _ := by ring
  have a2 : (nRk D : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 := pow_le_pow_left₀ (by positivity) hn' 7
  have a3 : (nRk D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 :=
    (pow_le_pow_left₀ (by positivity) hn' 3).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have a4 : 132 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc 132 * (t : ℝ) ^ 3 ≤ t * (t : ℝ) ^ 3 := by gcongr
      _ = (t : ℝ) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have a5 : (t : ℝ) ≤ (t : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have a6 : (t : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 * B := le_mul_of_one_le_right (by positivity) hB
  have a7 : (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D) ≤ (t : ℝ) ^ 7 * B := by gcongr
  have a8 : Real.sqrt D.R.m ≤ t := (Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩)
  have a9 : (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 3 := by
    calc (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 2 * t := by gcongr
      _ = _ := by ring
  unfold gap
  push_cast
  refine max_le (max_le ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_) ?_) ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_)
  · linarith
  · linarith
  · linarith

theorem hc_bounds (P : ParameterChoice' D L) (hS : SizesAt L) (hx : L.sc.x ≤ L.sc.X') (τ) (l : Fin D.R.m) :
    0 < (D.hc τ).b l ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg x0.le _)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.n_pos'
  have hb' : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hb0 : 0 < L.sc.b' := by unfold Scale.b' Scale.a; have : 0 < L.sc.X' := by linarith
                               positivity
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0.le x1.le
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb0.le x0 (by nlinarith)
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have he : L.etaSz < L.sc.w'' D.R.n := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x < L.sc.w'' D.R.n := div_lt_self hw0 x1
    have := L.etaSz_pos
    nlinarith
  have hwj : wj D (l.1 + 1) τ = (((D.hc τ).e l : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simp)]
    rfl
  have hbT : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have hLa : 0 ≤ L.LaG := (Real.rpow_nonneg x0.le _).trans hS.2.2.2.2.2.2.2.2.1.1
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos x1.le (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos; have := Real.log_nonneg x1.le; positivity
    unfold LevelStarExponents.rhoP at h2
    have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      linarith
    have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    nlinarith
  have key : L.sc.w'' D.R.n ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
    rw [← hwj]
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have := L.win_top (l.1 + 1) (by omega) l.2 τ ⟨t, ht1⟩ ht2.symm
      have a := L.bT_ge ⟨t, ht1⟩
      have b := hbT ⟨t, ht1⟩
      constructor <;> linarith [this.1, this.2]
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have := L.win_thick (l.1 + 1) (by omega) l.2 τ h2
        constructor <;> linarith [this.1, this.2]
      · have := L.win_thin (l.1 + 1) (by omega) l.2 τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith [this.1, this.2]
  refine ⟨?_, key.2⟩
  have := (abs_le.1 (L.be_close τ l l)).1
  push_cast at this
  have : (0 : ℝ) < (((D.hc τ).b l : ℚ) : ℝ) := by linarith [key.1]
  exact_mod_cast this

end Sizes

section Main

variable {D : D7} {L : SizeData₂ D}

set_option maxHeartbeats 1600000 in

theorem sizeRows_of (P : ParameterChoice' D L) (T : ParamsT D L P) (hC : P.CnW = 10) (hS : SizesAt L)
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ))
    (hm0 : Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ)) (hm1 : (D.R.m : ℝ) ≤ 2 * Real.sqrt (L.sc.x * L.sc.delta1))
    (hk : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ))
    (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) (hq : ((q0 D : ℕ) : ℝ) < L.sc.X') (hc : D.host.ccK = ⊤)
    (hz : 8 ≤ L.sc.x ^ (L.sc.eps / 4)) (hx : 44 ^ 4 ≤ L.sc.x) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have e0 := L.sc.eps_pos
  have e1 := L.sc.eps_lt
  have mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le x1.le h
  set z := L.sc.x ^ (L.sc.eps / 4) with hzdef
  have hL : L.sc.L = z ^ 4 := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; unfold Scale.L; congr 1; push_cast; ring
  have z3 : 512 ≤ z ^ 3 := by have := pow_le_pow_left₀ (by norm_num) hz 3; linarith
  have hLz : 512 * z ≤ L.sc.L := by rw [hL]; nlinarith only [hz, z3]
  set s := L.sc.x ^ ((1 : ℝ) / 4) with hsdef
  have hs4 : L.sc.x = s ^ 4 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; norm_num
  have s0 : 0 ≤ s := Real.rpow_nonneg x0.le _
  have s44 : 44 ≤ s := by
    by_contra h
    have := pow_lt_pow_left₀ (not_le.1 h) s0 (n := 4) (by norm_num)
    linarith
  have hδ : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos x1.le (by linarith)
  have hm2 : (D.R.m : ℝ) ≤ 2 * s ^ 2 := by
    refine hm1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩) (by norm_num))
    have : (s ^ 2) ^ 2 = L.sc.x := by rw [hs4]; ring
    rw [this]; exact mul_le_of_le_one_right x0.le hδ
  have m44 : 44 ≤ D.R.m := by
    have h1 : s ≤ Real.sqrt (L.sc.x * L.sc.delta1) := by
      refine Real.le_sqrt_of_sq_le ?_
      have a : s ^ 2 = L.sc.x ^ ((1 : ℝ) / 2) := by
        rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul x0.le]; norm_num
      have b : L.sc.x * L.sc.delta1 = L.sc.x ^ (1 + -(L.sc.eps / 8)) := by
        rw [Real.rpow_add x0, Real.rpow_one]; rfl
      rw [a, b]; exact mono _ _ (by linarith)
    exact_mod_cast (by linarith : (44 : ℝ) ≤ D.R.m)
  have hn2 : s ^ 8 * L.sc.L ≤ D.R.n := by
    refine le_trans ?_ ((mono (2 + L.sc.eps) _ (by linarith)).trans hn)
    rw [Real.rpow_add x0, Real.rpow_two]
    have : L.sc.x ^ 2 = s ^ 8 := by rw [hs4]; ring
    rw [this]; exact le_rfl
  have hk2 : s ^ 18 * L.sc.L ^ 2 ≤ D.R.k := by
    refine le_trans (le_of_eq ?_) ((mono (1 / 4 * (18 : ℕ) + L.sc.eps * (2 : ℕ)) _ (by push_cast; linarith)).trans hk)
    rw [Real.rpow_add x0, Real.rpow_mul x0.le, Real.rpow_mul x0.le, Real.rpow_natCast, Real.rpow_natCast]; rfl
  have L1 : 1 ≤ L.sc.L := by linarith
  have r1 := D.R.rank_add_five_le
  have r2 := D.R.three_m_lt_t
  have r3 := D.R.m_add_three_le_k
  have r4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have r5 : D.R.f = 2 * D.R.n := rfl
  have r6 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have n1 : 1 ≤ D.R.n := D.R.n_pos'
  have kt : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
  have nt : (D.R.n : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.n ≤ D.R.t)
  have ft : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have mt : (D.R.m : ℝ) + 1 ≤ D.R.t := by exact_mod_cast (by omega : D.R.m + 1 ≤ D.R.t)
  have t132 : (132 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 132 ≤ D.R.t)
  have n1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n1
  have k4 : (4 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 4 ≤ D.R.k)
  have q1 : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_le
  have d1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_le
  have cE : (LevelStarExponents.condE D : ℝ) = D.host.QS * D.host.q * D.host.d := by unfold LevelStarExponents.condE; push_cast; ring
  have qd1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := one_le_mul_of_one_le_of_one_le q1 d1
  have dc : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by
    rw [cE]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le (UpperTheory.Ram.Rd.one_le_QS_real D.host) q1)
  obtain ⟨-, -, c1, -, c2, -, c3, c4⟩ := hS.2.2.2.2.2.2.1
  have c1' : Real.log D.host.q ≤ z := c1.trans (mono _ _ (by unfold szTh; linarith))
  have c2' : Real.log D.host.d ≤ z := c2.trans (mono _ _ (by unfold szTh; linarith))
  have logt : Real.log D.R.t ≤ z := (Real.log_le_log (by linarith) P.t_le_eta).trans P.logeta
  have lrd : Real.log D.host.rdE ≤ Real.log (LevelStarExponents.condE D) := by
    rw [cE]; exact Real.log_le_log (UpperTheory.Ram.Rd.rdE_pos D.host) (UpperTheory.Ram.Rd.rdE_le_cond D.host)
  have lc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L / 100 := by
    rw [cE]
    have a := UpperTheory.Ram.Rd.log_cond_le D.host
    have b := Real.log_le_log (by linarith) nt
    linarith
  have b0 : 0 < L.sc.b := Real.exp_pos _
  set B := Real.sqrt L.sc.b with hBdef
  have hB2 : B ^ 2 = L.sc.b := Real.sq_sqrt b0.le
  have hcond : (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ B := by
    rw [hBdef, Real.sqrt_eq_rpow]; exact P.condE_le
  have c36 : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := le_self_pow₀ (by linarith) (by norm_num)
  have t9 : (D.R.t : ℝ) ^ 9 ≤ (D.R.t : ℝ) ^ 150 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hdB : (D.host.d : ℝ) * (D.R.t : ℝ) ^ 9 ≤ B :=
    (mul_le_mul (dc.trans c36) t9 (by positivity) (by positivity)).trans hcond
  have t9' : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 9 := one_le_pow₀ (by linarith)
  have htB : (D.R.t : ℝ) ^ 9 ≤ B := (le_mul_of_one_le_left (by positivity) d1).trans hdB
  have B1 : 1 ≤ B := t9'.trans htB
  have Bb : B ≤ L.sc.b := by nlinarith only [B1, hB2]
  have xX : L.sc.x ≤ L.sc.X' := by
    have a : L.sc.x ≤ D.R.k := by
      refine le_trans ?_ hk
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact mono _ _ (by linarith)
    have b : Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 3) :=
      (Real.log_le_log x0 (a.trans kt)).trans (logt.trans (mono _ _ (by linarith)))
    exact (Real.log_le_iff_le_exp x0).1 b
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) (by linarith)
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by linarith only [mul_nonneg (mul_pos x0 b0).le (sub_nonneg.2 n1')]
  have hSc : 4 * L.Sc ≤ L.sc.b := by nlinarith only [P.kS_le, L.Sc_pos, hw, k4]
  refine ⟨⟨P, T, hC⟩, hS, ?_, m44, ?_, ?_, ?_, fun i => ?_, ?_, lrd, lc, ?_, hc_bounds P hS xX, hc⟩
  · have a : (D.R.m : ℝ) ^ 4 ≤ (2 * s ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hm2 4
    have b : (D.R.f : ℝ) = 2 * D.R.n := by rw [r5]; push_cast; ring
    have c : 0 ≤ s ^ 8 := by positivity
    have : (D.R.m : ℝ) ^ 4 ≤ D.R.f := by
      have d : s ^ 8 * 8 ≤ s ^ 8 * L.sc.L := mul_le_mul_of_nonneg_left (by linarith) c
      linarith only [a, b, d, hn2]
    exact_mod_cast this
  · have a : (D.R.m : ℝ) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hm2 3
    have b : Real.log D.host.rdE ≤ L.sc.L := by linarith
    have c : 0 ≤ Real.log D.host.rdE := Real.log_nonneg c3
    have d : 8 ≤ s ^ 4 := by linarith
    calc L.sc.x ^ 2 * (D.R.m : ℝ) ^ 3 * L.sc.L * Real.log D.host.rdE ≤ L.sc.x ^ 2 * (2 * s ^ 2) ^ 3 * L.sc.L * L.sc.L := by gcongr
      _ = 8 * (s ^ 14 * L.sc.L ^ 2) := by rw [show L.sc.x ^ 2 = s ^ 8 by rw [hs4]; ring]; ring
      _ ≤ s ^ 4 * (s ^ 14 * L.sc.L ^ 2) := by gcongr
      _ = s ^ 18 * L.sc.L ^ 2 := by ring
      _ ≤ _ := hk2
  · have a : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by
      unfold Ranks.N; push_cast
      have : (D.R.m : ℝ) * (D.R.t + 1) ≤ D.R.t * (D.R.t + 1) := mul_le_mul_of_nonneg_right (by linarith only [mt]) (by positivity)
      nlinarith only [this, kt, t132, mul_nonneg (sub_nonneg.2 t132) (sq_nonneg (D.R.t : ℝ))]
    have m' : (D.R.m : ℝ) ≤ D.R.t := by linarith
    calc (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d ≤ D.R.t * D.R.t * ((D.R.t : ℝ) ^ 3) ^ 2 * D.host.d := by gcongr
      _ = D.host.d * (D.R.t : ℝ) ^ 8 := by ring
      _ ≤ D.host.d * (D.R.t : ℝ) ^ 9 := by gcongr; linarith; norm_num
      _ ≤ _ := hdB.trans Bb
  · calc D.R.f * D.R.m ≤ (D.R.r + 1) * (D.R.r + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (D.R.r + 1) ^ 2 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by norm_num)
  · have : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
    linarith [(Real.log_le_iff_le_exp this).2 (hg i)]
  · have : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    exact ((Real.log_le_iff_le_exp this).2 hq.le).trans (mono _ _ (by linarith))
  · have a := gap_le D B B1 (Real.sqrt_le_sqrt (by linarith [cloudLen_le L, L.Sc_pos])) m44
    have b : ((D.R.m : ℝ) + 1) * gap D 1 ≤ D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B) := by gcongr
    have c : 16 * (D.R.t : ℝ) ^ 8 ≤ B := by
      refine le_trans ?_ htB
      rw [pow_succ' _ 8]; gcongr; linarith
    have d : D.R.t * (4 * (D.R.t : ℝ) ^ 7 * B) = (16 * (D.R.t : ℝ) ^ 8) * B / 4 := by ring
    have e : (16 * (D.R.t : ℝ) ^ 8) * B ≤ B * B := by gcongr
    have f : B * B = L.sc.b := by rw [← hB2]; ring
    linarith only [b, d, e, f, hSc, Bb, B1]

theorem sizeRows_fam {eps : ℝ} (he : 0 < eps) (Fm : FamP eps) (h : FamHyp Fm) :
    ∃ x₀ : ℝ, ∀ x, Fm.x1 < x → x₀ ≤ x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i) := by
  refine ⟨max (44 ^ 4) ((8 : ℝ) ^ (4 / eps)), fun x hx h0 i => ?_⟩
  obtain ⟨⟨hn, -⟩, ⟨hm0, hm1⟩, hk, -⟩ := h.2.1 x hx i
  obtain ⟨hc, -, hg, -⟩ := h.1.2.2.2.2.2.2.2.2 x hx i
  have ex := Fm.L_x x i hx
  have ee := Fm.L_eps x i
  refine sizeRows_of (Fm.params x hx i) (Fm.parT x hx i) (Fm.fixed.2.2.2.2.2.2.2 x hx i).1 (Fm.sizes x hx i)
    (by rw [ex, ee]; exact hn) (by rw [ex]; exact hm0) (by rw [ex]; exact hm1) (by rw [ex, ee]; exact hk) hg
    (h.2.2.1 x hx i) hc ?_ (by rw [ex]; exact le_of_max_le_left h0)
  rw [ex, ee]
  have e1 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e1]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right h0) (by positivity)

theorem sizeAt : SizeAt :=
  ⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ =>
    let ⟨x₀, h⟩ := sizeRows_fam he Fm hF
    ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩

end Main

end GlobalTheory.BigTop.Fun.SizeProof

end
