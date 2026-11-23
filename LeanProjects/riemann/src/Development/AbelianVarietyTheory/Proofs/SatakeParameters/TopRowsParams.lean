import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopRows

theorem nuRow_tauPl_of_isTopPl {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (z : Bool × HH D) (hz : IsTopPl D z) :
    DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) = (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) ∧
    0 ≤ DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ∧
    DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) ≤ L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨hz1, hz2⟩ := hz
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hτ : (D.eTau (tauPl D z) : D.R.GG) = D.R.tau1 (⟨z.2, hz2⟩ : D.host.TT) := by
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]
  obtain ⟨hu1, huk⟩ := L.top_u (tauPl D z) ⟨z.2, hz2⟩ hk hτ
  obtain ⟨-, hw⟩ := L.win_top (j + 1) (by omega) (by omega) (tauPl D z) ⟨z.2, hz2⟩ hτ
  have ha : aL L z.2 = L.aT ⟨z.2, hz2⟩ := by unfold aL; rw [dif_pos hz2]
  have hb : bL L z.2 = L.bT ⟨z.2, hz2⟩ := by unfold bL; rw [dif_pos hz2]
  have hwe : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have hkc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e1 : DV.nuRow D u (j + 1) (tauPl D z) 0 = (aL L z.2 : ℝ) + (wPl D (j + 1) z - kaJ D (j + 1)) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ 0 hk, D.hcW_first u _ hk, ha, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [hu1]
    ring
  have e2 : DV.nuRow D u (j + 1) (tauPl D z) (D.R.k - 1) =
      (wPl D (j + 1) z - kaJ D (j + 1)) - (bL L z.2 : ℝ) := by
    rw [RowWeightLemmas.nuRow_head D u j hj _ (D.R.k - 1) (by omega), D.hcW_last u _ hk, hb, hwe]
    unfold kaJ Ranks.N
    push_cast
    rw [huk, hkc]
    ring
  refine ⟨e1, e2, (RowWeightLemmas.nuRow_pos D u j hj _ _ (by unfold Ranks.N; omega)).le, ?_⟩
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  rw [e2, hb]
  change wPl D (j + 1) z ≤ _ at hw
  linarith

theorem eta_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.etaSz ≤ L.sc.b' / L.sc.x := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h1 : L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    le_mul_of_one_le_left L.etaSz_pos.le (by nlinarith)
  have h2 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le hx (le_mul_of_one_le_right hx.le hn1)
  exact h1.trans (P.mteta.trans h2)

theorem top_rows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro eps Fm
  refine ⟨0, fun x _ hx1 i u j hj z hz => ?_⟩
  have h4 := eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

end GlobalTheory.TopRows
