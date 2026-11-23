import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem wts_U_le_h0_of_large : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  intro D L P5 j τ hL hv a ha
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hS := L.Sc_pos
  have hη := L.etaSz_pos
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    exact div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)
  have hn : (1 : ℝ) ≤ D.R.n := by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)
  have hU0 := U_nonneg L j τ 0 (by have := rank_eq j; omega)
  have hUa := liftWeightCombinatorialData_U_le_U_zero L j τ a ha
  have hv0 := hv.1 0 (by omega)
  have hcl := L.cloud_v τ ⟨0, by omega⟩
  have hc := c_le L j τ hv

  have ePb : (parOf L j).b = L.sc.b := rfl
  have eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hbb' := hL.bb'
  have htop := hL.top_le
  simp only [parOf] at hbb' htop
  change 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'

  have hm1 : 1 ≤ D.R.m := by omega
  have key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨
      wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz := by
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have hw := (L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2
      have hbt := P5.bT_le ⟨t, ht1⟩
      have hr := P5.rho_le
      unfold LevelStarExponents.rhoP at hr
      have hLa : 0 < L.LaG := by
        have h := P5.S_le
        by_contra hc'
        push_neg at hc'
        have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)
        linarith
      have hNs : 0 ≤ LevelStarExponents.Nstar L := by
        unfold LevelStarExponents.Nstar Scale.delta1; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by positivity
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        rw [hx2] at hr
        linarith
      have h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b' :=
        mul_le_mul_of_nonneg_right h5 hb0.le
      right
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b' := by ring
      rw [this]
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · exact Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2
      · have hw := (L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2
        right
        have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := by
          unfold Scale.w''
          rw [div_le_iff₀ (by positivity)]
          have hxn : 1 ≤ L.sc.x * (D.R.n : ℝ) := by nlinarith
          have := mul_le_mul_of_nonneg_left hxn hb0.le
          linarith
        have hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2) := by positivity
        nlinarith
  have hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h := by
    rw [eh]
    rcases key with h | h
    · nlinarith
    · have h2b : 2 * L.sc.b' < L.sc.b := by
        have : 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' := by
          have : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ) := by nlinarith
          nlinarith
        linarith
      linarith
  have hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j) := by
    unfold Formalism.CohomologicalDescent.ShortWeightBounds.h0
    apply Nat.le_floor
    have : (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hU0
    rw [this]; exact hU0h
  omega

end GlobalTheory.ExpTie.Lift
