import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.N0LeNs
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NusOffLevel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin.RecordRun

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin GlobalTheory.RunJoin.Inh GlobalTheory.RunJoin.InhAll GlobalTheory.FinalJoin

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} {j : ℕ}

theorem exists_thick (L : SizeData₂ D) : ∃ τ : D.what₂.Tau, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
  classical
  have h := L.thickDensity_pos
  rw [L.typeDensity_eq_card_div] at h
  have h1 : 0 < D.host.T2.card := by
    rcases Nat.eq_zero_or_pos D.host.T2.card with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  obtain ⟨s, hs⟩ := Finset.card_pos.1 h1
  refine ⟨D.eTau.symm ⟨D.R.tau2 (D.R.dig s + D.host.u0), rfl⟩, ?_⟩
  rw [Equiv.apply_symm_apply]
  unfold Host.thickPlaces
  exact Finset.mem_image.2 ⟨s, hs, rfl⟩

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  unfold Scale.b' Scale.a Scale.X' Scale.b
  positivity

theorem teta_le_wj (P : ParameterChoice' D L) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    (D.R.t : ℝ) * L.etaSz ≤ wj D j τ := by
  obtain ⟨τ0, h0⟩ := exists_thick L
  have a1 := (L.win_thick j h1 h2 τ0 h0).1
  have a2 := P.X''_ratio j j τ0 τ h1 h2 h1 h2
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb := b_pos L
  have hn : (0 : ℝ) < D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have hb' := b'_pos L
  have hw : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  refine P.teta.trans ?_
  have a3 := a1.trans a2
  unfold Scale.X'' Scale.a at a3
  rw [div_mul_eq_mul_div, le_div_iff₀ hw] at a3
  rw [div_le_iff₀ hx]
  refine le_of_mul_le_mul_left ?_ hb
  linarith

theorem k_b'_le (P : ParameterChoice' D L) (hx : 3 ≤ L.sc.x) : (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b := by
  have h := P.rbS
  have hk := P.k_ge_m2L
  have hb' := b'_pos L
  have hb := b_pos L
  have hS := L.Sc_pos
  have hd := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hL := one_le_L L
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have := D.R.two_le_m
    exact_mod_cast (by unfold Ranks.r; omega : D.R.k ≤ D.R.r)
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hlog : 1 ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hA : (D.R.m : ℝ) ≤ LevelStarExponents.lA L := by
    unfold LevelStarExponents.lA
    rw [le_div_iff₀ (by positivity)]
    have e : L.sc.x ^ L.sc.eps = L.sc.L := rfl
    rw [e]
    calc (D.R.m : ℝ) * (D.R.m * L.de2) ≤ D.R.m * (D.R.m * 1) := by gcongr
      _ = (D.R.m : ℝ) ^ 2 * 1 := by ring
      _ ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := by gcongr
      _ ≤ D.R.k * 1 := by linarith
      _ ≤ _ := by gcongr
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < D.R.m by linarith)
  calc (D.R.m : ℝ) * (D.R.k * L.sc.b') = D.R.k * L.sc.b' * 1 * D.R.m := by ring
    _ ≤ D.R.r * (L.sc.b' + L.Sc) * Real.log L.sc.x * LevelStarExponents.lA L := by gcongr; linarith
    _ ≤ L.de2 * D.R.m * L.sc.b := h
    _ ≤ 1 * D.R.m * L.sc.b := by gcongr
    _ = _ := by ring

theorem aP_eq_rat (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : ((kaR T hK j).aP τ i : ℝ) = ((DV.sigPar D τ i : ℚ) : ℝ) + wj D j τ -
      ((D.R.k : ℝ) + j - 1 - 1 - i.1) - ((D.R.t : ℝ) + 1) / 2 := by
  have e1 := kaWt_big D hK (even_nV T) j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  rw [← e1, DV.aPlusQ_eq] at e2
  unfold DV.eQ at e2
  rw [dif_pos ⟨h1, h2⟩] at e2
  have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
  push_cast at e3
  unfold kaR wj
  rw [dif_pos (by omega : j - 1 < D.R.m)]
  exact e3

theorem G_le (T : ParamsT D L P) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ((Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) : ℕ) : ℝ) ≤ LevelStarExponents.h0 L ∧
    ((Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) : ℕ) : ℝ) ≤ (D.s.Del : ℝ) := by
  unfold Tp
  rw [GlobalTheory.RunNuTest.dim_eq T h1 h2]
  push_cast
  have a1 : 40 * ((T.Dp : ℝ) + 2) ≤ T.TO := by exact_mod_cast T.TO_40
  have a2 : 2 * (D.R.r : ℝ) ≤ T.TO := by
    have := T.TO_nW
    exact_mod_cast (by omega : 2 * D.R.r ≤ T.TO)
  have a3 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have a4 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have a5 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  constructor
  · have := T.heightBound_ge_order_sq
    calc ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * D.R.r) ≤ (3 / 2 * T.TO) * (5 / 2 * T.TO) := by
          gcongr <;> linarith
      _ ≤ _ := by nlinarith [sq_nonneg (T.TO : ℝ)]
  · refine le_trans ?_ T.Del_gap
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have : D.R.m * 1 ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    gcongr

theorem h0_le_etaSz (L : SizeData₂ D) : LevelStarExponents.h0 L ≤ L.etaSz := by
  unfold LevelStarExponents.h0
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  exact div_le_self L.etaSz_pos.le (by linarith)

theorem sigPar_gap (P : ParameterChoice' D L) (τ : D.what₂.Tau) {G : ℝ} (g1 : G ≤ LevelStarExponents.h0 L) (g2 : G ≤ (D.s.Del : ℝ))
    (i : ℕ) (hi : i + 1 < D.R.k + D.R.m - 1) :
    G ≤ ((DV.sigPar D τ i : ℚ) : ℝ) - ((DV.sigPar D τ (i + 1) : ℚ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases c1 : i + 1 < D.R.k - 1
  · rw [dif_pos c1, dif_pos (by omega)]
    have h2 := D.s.cloud_gap D.u₀ τ i c1
    simp only [D.hcW_v] at h2
    have h3 := congrArg (fun q : ℚ => (q : ℝ)) h2
    have h4 : (0 : ℝ) ≤ ((D.s.Del : ℚ) : ℝ) := by exact_mod_cast D.s.Del_pos.le
    push_cast at h3
    linarith
  · by_cases c2 : i < D.R.k - 1
    · rw [dif_pos c2, dif_neg c1, dif_pos (by omega)]
      have a1 := (L.cloud_v τ ⟨i, c2⟩).1
      have a2 := teta_le_wj P le_rfl (show 1 ≤ D.R.m by omega) τ
      unfold wj at a2
      rw [dif_pos (by omega)] at a2
      have a3 := (abs_le.1 (L.be_close τ ⟨i + 1 - (D.R.k - 1), by omega⟩ ⟨1 - 1, by omega⟩)).1
      have a4 : (2 : ℝ) ≤ D.R.t := by
        have := D.R.rank_add_five_le
        exact_mod_cast (by omega : 2 ≤ D.R.t)
      have a5 := h0_le_etaSz L
      have a6 := mul_le_mul_of_nonneg_right a4 L.etaSz_pos.le
      push_cast at a3 ⊢
      linarith
    · rw [dif_neg c2, dif_neg c1, dif_pos (by omega), dif_pos (by omega)]
      have a1 := (P.nodes_gap τ (i - (D.R.k - 1)) (by omega)).1
      have e : (⟨i - (D.R.k - 1) + 1, by omega⟩ : Fin D.R.m) = ⟨i + 1 - (D.R.k - 1), by omega⟩ :=
        Fin.ext (by show i - (D.R.k - 1) + 1 = i + 1 - (D.R.k - 1); omega)
      rw [e] at a1
      push_cast at a1 ⊢
      linarith

theorem gapP (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (h : i.1 + 1 < (D.R.sigW j).1) :
    ((Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ ((kaR T hK j).aP τ) i + 2 := by
  obtain ⟨g1, g2⟩ := G_le T h1 h2
  have h' : i.1 + 1 < D.R.k + j - 1 := h
  have a := sigPar_gap P τ g1 g2 i.1 (by omega)
  have e1 := aP_eq_rat T hK h1 h2 τ i
  have e2 := aP_eq_rat T hK h1 h2 τ ⟨i.1 + 1, h⟩
  unfold gapZ
  rw [dif_pos h]
  generalize Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) = G at a ⊢
  push_cast at e2
  have : (G : ℝ) ≤ ((kaR T hK j).aP τ i : ℝ) - ((kaR T hK j).aP τ ⟨i.1 + 1, h⟩ : ℝ) + 2 := by linarith
  exact_mod_cast this

theorem gapM (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).2) (h : i.1 + 1 < (D.R.sigW j).2) :
    ((Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ ((kaR T hK j).aM τ) i + 2 := by
  obtain ⟨g1, -⟩ := G_le T h1 h2
  have hs : (D.R.sigW j).2 = D.R.m - j := rfl
  have key : ∀ (c : Fin (D.R.sigW j).2) (n : ℕ) (hn : j + n < D.R.m), c.1 + 1 + n = D.R.m - j →
      ((kaR T hK j).aM τ c : ℝ) = (((D.hc τ).b ⟨j + n, hn⟩ : ℚ) : ℝ) - ((DV.eQ D j τ : ℚ) : ℝ) -
        ((D.R.t : ℝ) + 1 + 2 * n) / 2 := by
    intro c n hn hc
    have e1 := kaWt_small D hK (even_nV T) j h1 h2 τ c
    have e2 := (hK j h1 h2 τ).2 (Fin.rev c)
    have e0 : ((Fin.rev c : Fin _) : ℕ) = n := by rw [Fin.val_rev]; omega
    rw [e0] at e2
    unfold DV.aMinusQ at e2
    rw [dif_pos hn] at e2
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    have e4 := congrArg (fun q : ℤ => (q : ℝ)) e1
    push_cast at e3 e4
    unfold kaR
    linarith
  obtain ⟨n, hn⟩ : ∃ n, i.1 + 1 + 1 + n = D.R.m - j := ⟨D.R.m - j - (i.1 + 2), by omega⟩
  have e1 := key i (n + 1) (by omega) (by omega)
  have e2 := key ⟨i.1 + 1, h⟩ n (by omega) hn
  have a : LevelStarExponents.h0 L ≤ (((D.hc τ).b ⟨j + (n + 1), by omega⟩ - (D.hc τ).b ⟨j + n, by omega⟩ : ℚ) : ℝ) :=
    (P.nodes_gap τ (j + n) (by omega)).1
  unfold gapZ
  rw [dif_pos h]
  generalize Tp D j T.TO * (Tp D j T.TO + 2 * D.R.r) = G at g1 ⊢
  push_cast at e1 a
  have : (G : ℝ) ≤ ((kaR T hK j).aM τ i : ℝ) - ((kaR T hK j).aM τ ⟨i.1 + 1, h⟩ : ℝ) + 2 := by linarith
  exact_mod_cast this

theorem b_le_size (T : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    L.sc.b ≤ (kaR T hK j).size := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  obtain ⟨τ, h0⟩ := exists_thick L
  have a1 := (L.win_thick j h1 h2 τ h0).1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have e := aP_eq_rat T hK h1 h2 τ ⟨0, hp⟩
  unfold DV.sigPar at e
  rw [dif_pos (show 0 < D.R.k - 1 by omega)] at e
  have a2 := (L.cloud_v τ ⟨0, show 0 < D.R.k - 1 by omega⟩).1
  have a3 : (kaR T hK j).aP τ ⟨0, hp⟩ ≤ WeightAlgebra.DF (kaR T hK j) := by
    unfold WeightAlgebra.DF degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (kaR T hK j).aP τ i) + ∑ i, (kaR T hK j).aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
    exact le_add_right (Finset.single_le_sum (f := (kaR T hK j).aP τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have a4 : ((kaR T hK j).aP τ ⟨0, hp⟩ : ℝ) ≤ WeightAlgebra.DF (kaR T hK j) := by exact_mod_cast a3
  have hn : (kaR T hK j).n = D.R.nV := kaWt_n _ _ _ _
  have a5 : (D.R.k : ℝ) + j + D.R.t ≤ (D.R.nV : ℝ) + 1 := by
    exact_mod_cast (by unfold Ranks.nV Ranks.r; omega : D.R.k + j + D.R.t ≤ D.R.nV + 1)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hm := one_le_mu (D := D) (j := j)
  have a6 : (D.R.nV : ℝ) ≤ D.R.f * mu D j * D.R.r * D.R.nV := by
    refine le_mul_of_one_le_left (Nat.cast_nonneg _) ?_
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hm) (by linarith)
  have a7 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  rw [size_eq, hn]
  push_cast at e
  linarith

theorem le_of_gaps {p : ℕ} (u a : Fin p → ℕ) (c K : ℤ) (h : ∀ i, gapZ u i ≤ c * gapZ a i + K) (hK : 0 ≤ K) (i : Fin p) :
    (u i : ℤ) ≤ c * a i + p * K := by
  have key : ∀ n (i : Fin p), p - i.1 = n + 1 → (u i : ℤ) ≤ c * a i + ((n : ℤ) + 1) * K := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have := h i
      have hn : ¬ i.1 + 1 < p := by omega
      simpa [gapZ, hn] using this
    | succ n ih =>
      intro i hi
      have := h i
      have hn : i.1 + 1 < p := by omega
      have e := ih ⟨i.1 + 1, hn⟩ (by show p - (i.1 + 1) = n + 1; omega)
      simp only [gapZ, dif_pos hn] at this
      push_cast
      linarith
  have h1 := key (p - i.1 - 1) i (by have := i.2; omega)
  have h2 : (((p - i.1 - 1 : ℕ) : ℤ) + 1) ≤ p := by have := i.2; omega
  exact h1.trans (add_le_add_right (mul_le_mul_of_nonneg_right h2 hK) _)

theorem gapZ_sub {p : ℕ} {u a w : Fin p → ℕ} {T : ℤ} (h : ∀ i, (u i : ℤ) = a i - T * w i) (i : Fin p) :
    gapZ u i = gapZ a i - T * gapZ w i := by
  unfold gapZ
  split_ifs with hi
  · rw [h, h]; ring
  · exact h i

theorem rem_le (x : ℤ) (T d : ℕ) :
    x - T * Int.fdiv x ((T + d + 2 : ℕ) : ℤ) ≤ ((d : ℤ) + 2) * Int.fdiv x ((T + d + 2 : ℕ) : ℤ) + (T + d + 2) := by
  have hp : (0 : ℤ) < ((T + d + 2 : ℕ) : ℤ) := by positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have := Int.lt_mul_ediv_self_add (x := x) hp
  generalize x / ((T + d + 2 : ℕ) : ℤ) = g at this ⊢
  push_cast at this
  linarith

theorem DF_wF_le {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hL : IsL D ka wL T nW)
    (hF : IsF' ka wL wF T nP) (hT : (WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r ≤ T) (hT' : WeightFamilies.dimY D j + 2 ≤ T) :
    WeightAlgebra.DF wF ≤ (WeightFamilies.dimY D j + 2) * WeightAlgebra.DF wL + D.R.f * (D.R.r ^ 2 * (3 * T)) := by
  have t1 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hT
  have t2 : (WeightFamilies.dimY D j : ℤ) + 2 ≤ T := by exact_mod_cast hT'
  have t3 : (0 : ℤ) ≤ T := by positivity
  have hP : ∀ τ i, wF.aP τ i ≤ (WeightFamilies.dimY D j + 2) * wL.aP τ i + (D.R.sigW j).1 * (3 * T) := by
    intro τ i
    have := le_of_gaps (wF.aP τ) (wL.aP τ) ((WeightFamilies.dimY D j : ℤ) + 2) (3 * T) (fun i => by
      rw [gapZ_sub (hF.2.1 τ), hL.2.1 τ i]
      unfold Tp
      split_ifs with hi
      · have := rem_le (gapZ (ka.aP τ) i + 2) T (WeightFamilies.dimY D j)
        linarith
      · have := rem_le ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) T (WeightFamilies.dimY D j)
        have e : gapZ (ka.aP τ) i = ka.aP τ i := by unfold gapZ; rw [dif_neg hi]
        rw [e]
        linarith) (by positivity) i
    exact_mod_cast this
  have hM : ∀ τ i, wF.aM τ i ≤ (WeightFamilies.dimY D j + 2) * wL.aM τ i + (D.R.sigW j).2 * (3 * T) := by
    intro τ i
    have := le_of_gaps (wF.aM τ) (wL.aM τ) ((WeightFamilies.dimY D j : ℤ) + 2) (3 * T) (fun i => by
      rw [gapZ_sub (hF.2.2 τ), hL.2.2 τ i]
      unfold Tp
      split_ifs with hi
      · have := rem_le (gapZ (ka.aM τ) i + 2) T (WeightFamilies.dimY D j)
        linarith
      · have := rem_le (ka.aM τ i : ℤ) T (WeightFamilies.dimY D j)
        have e : gapZ (ka.aM τ) i = ka.aM τ i := by unfold gapZ; rw [dif_neg hi]
        rw [e]
        linarith) (by positivity) i
    exact_mod_cast this
  have hs := sig_add h1 h2
  have hτ : ∀ τ, (∑ i, wF.aP τ i) + ∑ i, wF.aM τ i ≤
      (WeightFamilies.dimY D j + 2) * ((∑ i, wL.aP τ i) + ∑ i, wL.aM τ i) + D.R.r ^ 2 * (3 * T) := by
    intro τ
    have b1 := Finset.sum_le_sum (s := Finset.univ) fun i _ => hP τ i
    have b2 := Finset.sum_le_sum (s := Finset.univ) fun i _ => hM τ i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at b1 b2
    rw [← hs]
    nlinarith [Nat.zero_le ((D.R.sigW j).1 * (D.R.sigW j).2 * T)]
  unfold WeightAlgebra.DF degP
  refine (Finset.sum_le_sum fun τ _ => hτ τ).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, smul_eq_mul]

section Record

variable (T : ParamsT D L P) (hK : DV.KapDef D) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) (hx : 3 ≤ L.sc.x)
  (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
include h1 h2

include hx in
theorem DF_ka_le : (WeightAlgebra.DF (kaR T hK j) : ℝ) ≤ 4 * ((D.R.k : ℝ) * D.R.f * L.sc.b) := by
  have a := (GlobalTheory.RunDepth.DF_kaR_le D L P T hK hx (k_b'_le P hx) j ⟨h1, h2⟩).1
  have b := (GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L P hx (k_b'_le P hx)).1
  refine a.trans ?_
  calc (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))
      ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (2 * L.sc.b)) := by gcongr
    _ = _ := by ring

omit h1 h2 in
theorem T_DF_le : (T.TO : ℝ) * WeightAlgebra.DF (lR T hK j) ≤ WeightAlgebra.DF (kaR T hK j) := by
  obtain ⟨τ, -⟩ := exists_thick L
  exact_mod_cast (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L P T hK j τ).2.2

include S hZ hx in
theorem ka_size_le : (kaR T hK j).size ≤ 7 * ((D.R.k : ℝ) * D.R.f * L.sc.b) := by
  have hR := rn_of T S hZ
  have a1 := DF_ka_le T hK hx h1 h2
  have a2 := extra_le hR (mu_le_r (D := D) (j := j))
  have hb := hR.b_pos
  have a3 := mul_le_mul_of_nonneg_right (A_le_kf (D := D)) hb.le
  have a4 := hR.b_le_Ab
  have a5 : (2 : ℝ) ≤ L.sc.b := le_trans (by norm_num) hR.toBs.b_ge
  rw [size_eq, show (kaR T hK j).n = D.R.nV from kaWt_n _ _ _ _, enV T]
  linarith

omit h1 h2 in
theorem T_wL_le : (T.TO : ℝ) * (lR T hK j).size ≤ (kaR T hK j).size + T.TO := by
  have a1 := T_DF_le (j := j) T hK
  have hm := one_le_mu (D := D) (j := j)
  have h4 : (0 : ℝ) ≤ (D.R.f : ℝ) * mu D j * D.R.r * T.nP := by positivity
  rw [size_eq, size_eq, show (kaR T hK j).n = D.R.nV from kaWt_n _ _ _ _, enV T, show (lR T hK j).n = T.nWn from rfl]
  linarith

include S hZ in
theorem wF_size_le : (fR T hK j).size ≤
    ((WeightFamilies.dimY D j : ℝ) + 2) * (lR T hK j).size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T.TO := by
  have hR := rn_of T S hZ
  obtain ⟨-, -, hL, hF, -⟩ := GlobalTheory.RunNuTest.weights T hK h1 h2
  have hd := GlobalTheory.RunNuTest.dim_eq T h1 h2
  have a0 := DF_wF_le h1 h2 hL hF (by rw [hd]; exact T.TO_nW) (by rw [hd]; have := T.TO_40; omega)
  have a1 : (WeightAlgebra.DF (fR T hK j) : ℝ) ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * WeightAlgebra.DF (lR T hK j) + D.R.f * ((D.R.r : ℝ) ^ 2 * (3 * T.TO)) := by
    exact_mod_cast a0
  have hm := one_le_mu (D := D) (j := j)
  have hm2 := mu_le_r (D := D) (j := j)
  have hn : (T.nP : ℝ) ≤ T.TO := hR.nPW.trans hR.nW_le
  have a2 : (D.R.f : ℝ) * mu D j * D.R.r * T.nP ≤ (D.R.f : ℝ) * D.R.r * D.R.r * T.TO := by gcongr
  have a3 : (0 : ℝ) ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * (D.R.f * mu D j * D.R.r * T.nWn) := by positivity
  have a4 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
  have a5 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.r * T.TO := by positivity
  rw [size_eq, size_eq, show (fR T hK j).n = T.nP from rfl, show (lR T hK j).n = T.nWn from rfl]
  linarith

include S hZ hx in
theorem DF_wL_le : (WeightAlgebra.DF (lR T hK j) : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  have hR := rn_of T S hZ
  have a1 := DF_ka_le T hK hx h1 h2
  have a2 := T_DF_le (j := j) T hK
  have a3 : (2 : ℝ) ≤ T.TO := by linarith [hR.forty_mul_degree_le_order, hR.two_le_degree_alt]
  have a4 := mul_le_mul_of_nonneg_right a3 (Nat.cast_nonneg (α := ℝ) (WeightAlgebra.DF (lR T hK j)))
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have := D.R.two_le_m
    exact_mod_cast (by unfold Ranks.r; omega : D.R.k ≤ D.R.r)
  have hb := hR.b_pos
  have a5 : (D.R.k : ℝ) * D.R.f * L.sc.b ≤ D.R.r * D.R.f * L.sc.b := by gcongr
  linarith

include S hZ hx in
theorem setC_of {B : WeightFamilies.Prov D} {Q : ModuliIntegralCharts.Prov D} (X : PJ D B Q j) (hO : OPO L B) {C A : ℝ} (hD : DomAt D L j T.nWn C) :
    SetC L X 10 C A (kaR T hK j) (lR T hK j) (fR T hK j) T.TO T.nP T.nWn (LevelStarExponents.h0 L - 4) := by
  have hR := rn_of T S hZ
  obtain ⟨-, -, hL, hF, -⟩ := GlobalTheory.RunNuTest.weights T hK h1 h2
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.RunCounterexample.clauses_at_shifted_gap T hK h1 h2
  have hd := GlobalTheory.RunNuTest.dim_eq T h1 h2
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb := hR.b_pos
  have hTO1 := hR.one_le_order_alt
  have hkfb : 0 ≤ (D.R.k : ℝ) * D.R.f * L.sc.b := by positivity
  have hs := ka_size_le T hK S hZ hx h1 h2
  have hn : (kaR T hK j).n = D.R.nV := kaWt_n _ _ _ _
  refine ⟨hn, gapP T hK h1 h2, gapM T hK h1 h2, c1, fun τ => ?_, c2, c3, by linarith, T.even_nP₂, T.nP_ge, T.nW_lo.2.2, ?_,
    T.nW_lo.1, T.split, hL, hF, ?_, by have := T.TO_40; omega, ?_, ?_, ?_, T.nW_40, ?_, ?_, hO, hD⟩
  · have hp : 0 < (D.R.sigW j).1 := by
      have := D.R.m_add_three_le_k
      show 0 < D.R.k + j - 1
      omega
    have a := c2 τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
    have e : (((kaR T hK j).aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ : ℕ) : ℤ) + D.R.t + 1 ≤ ncAt (kaR T hK j) τ := by
      unfold ncAt
      rw [dif_pos hp, sig_add h1 h2, hn]
      unfold Ranks.nV
      push_cast
      split_ifs
      · have := Int.natCast_nonneg ((kaR T hK j).aM τ ⟨(D.R.sigW j).2 - 1, by omega⟩)
        linarith
      · linarith
    have e' : (((kaR T hK j).aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ : ℕ) : ℝ) + D.R.t + 1 ≤ (ncAt (kaR T hK j) τ : ℝ) := by
      exact_mod_cast e
    linarith [sq_nonneg (T.TO : ℝ)]
  · unfold sizeConstantAtParamsWeight
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · rw [le_div_iff₀ (by linarith)]
    have a1 := T_wL_le (j := j) T hK
    have a2 : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
    have a3 := mul_le_mul_of_nonneg_right (A_le_kf (D := D)) hb.le
    have a4 := hR.b_le_Ab
    linarith
  · rw [hd]; have := T.TO_40; omega
  · rw [hd]; exact T.TO_40
  · rw [hd]; exact T.TO_nW
  · refine (n0_le_Ns h1 h2).trans ?_
    rw [show Dm D = T.Dp from dm_eq T]
    exact T.order_ge_rank_bound
  · rw [hd]; exact T.TO_11D2

end Record

theorem pageRun_record (T : ParamsT D L P) (hK : DV.KapDef D) (S : SizesAt L) (hCnW : P.CnW = 10)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x)
    (hC : 1000 ≤ T.CP) (hCZ : T.CP ^ 20 ≤ zBase L) (B : WeightFamilies.Prov D) (Q : ModuliIntegralCharts.Prov D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (X : PJ D B Q j) (hO : OPO L B) :
    PageRun L X ⟨10, 20, T.CP, T.eP, T.CP, T.eP, 7⟩ T.CP T.eP L.Ct (kaR T hK j) (lR T hK j) (fR T hK j)
      T.TO T.nP T.nWn (LevelStarExponents.h0 L - 4) := by
  have hZ : 10 ^ 60 ≤ zBase L := by
    refine le_trans ?_ hCZ
    calc (10 : ℝ) ^ 60 = 1000 ^ 20 := by norm_num
      _ ≤ _ := by gcongr
  have hx3 : 3 ≤ L.sc.x := le_trans (by norm_num) hx
  have hR := rn_of T S hZ
  have hD : DomAt D L j T.nWn T.CP := domAt_index h1 h2 ((domAt_of P T S hCnW hg hx).mono hC hCZ)
  have hset := setC_of T hK S hZ hx3 h1 h2 X hO (A := T.eP) hD
  have hd0 : (0 : ℝ) ≤ (WeightAlgebra.DF (lR T hK j) : ℝ) := Nat.cast_nonneg _
  have hd := DF_wL_le T hK S hZ hx3 h1 h2
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
    calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 := by gcongr
      _ = (D.R.k : ℝ) ^ 4 := by ring
  obtain ⟨n1, n2, n3⟩ := nums hR.toBs (r := D.R.r) (Nat.cast_nonneg _) (by have := hR.rA; have := hR.r6; linarith) hd0
    hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
  obtain ⟨-, -, c3, -, -, -⟩ := third_hypothesis_of_params T S hZ
  obtain ⟨-, -, -, d4, -, -⟩ := fourth_hypothesis_of_params T S hZ
  have d1 := b_le_size T hK h1 h2
  refine ⟨⟨parA_of P S hg hx, hset, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨d1, ?_, wF_size_le T hK S hZ h1 h2, d4, ?_, fun i => ?_⟩,
    T.TO_poly⟩, ⟨P, T, S, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, T.eP_ge⟩⟩
  · rw [Real.rpow_zero, one_mul, eRR7, WeightFamilies.PPv_rec T]; exact n1
  · rw [Real.rpow_zero, one_mul, eRR7, WeightFamilies.PPv_rec T, eg0]; exact n2
  · rw [dimY_eq_top h1 h2]; exact c3
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 7 * WeightFamilies.PPv D L T.CP T.eP * (WeightAlgebra.DF (lR T hK j) : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR7, WeightFamilies.PPv_rec T, eg0, ← mul_div_assoc, div_mul_eq_mul_div, div_le_one hq0]
    linarith
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 7 ^ 2 *
      (WeightFamilies.RRv D 7 * WeightFamilies.PPv D L T.CP T.eP * (WeightAlgebra.DF (lR T hK j) : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR7, WeightFamilies.PPv_rec T, ← mul_div_assoc, div_le_iff₀ hq0]
    linarith
  · rw [GlobalTheory.RunNuTest.dim_eq T h1 h2]
    have := hR.h3f hd0 hd hq
    linarith
  · have a1 := T_wL_le (j := j) T hK
    have a2 : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
    linarith
  · rw [WeightFamilies.PPv_rec T, eRR7, ← hR.sb_sq]
    exact mul_le_mul (hR.toBs.rd_pow_le (by norm_num)) hR.toBs.PP_le_sb hR.PP_pos.le hR.sb_pos.le
  · have a := (GlobalTheory.RunDepth.DF_kaR_le D L P T hK hx3 (k_b'_le P hx3) j ⟨h1, h2⟩).2 i
    have : 2 * (WeightAlgebra.DF (kaR T hK j) : ℝ) + 2 < D.host.g i := by linarith
    exact_mod_cast this

end GlobalTheory.FinalJoin.RecordRun
