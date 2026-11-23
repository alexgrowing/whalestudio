import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHFrameDtPackPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions.Examples₂ GlobalTheory.EX.WinLow

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dif_pos hN]
  push_cast
  rw [lamOf_eq p j hj, lamOf_eq p j hj, wtQ_eq_wtN, wtQ_eq_wtN]
  have a1 : wtN p (R.N R.m - 1) ≤ wtN p (R.N j - 1) := wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : blkN R (R.N R.m - 1) < R.m := by omega
    unfold wtN
    rw [dif_neg c1, dif_pos c2]
    have e : (⟨blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold wtN
    rw [dif_pos hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

theorem hcW_injective {s : Scale} {C : FC} {cD ch : ℝ} {P : PreCh} {q1 : ℕ} {a b : P.R.A → ℤ}
    {c : P.Word → Fin (P.R.k - 2) → Bool} (h : ChOK s C cD ch P q1 a b c) : Function.Injective P.hcW := by
  intro u u' huu
  apply h.inj
  funext l
  have hD : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _)
    exact_mod_cast this
  have e1 := h.code u (placeNo P.H 0) l.1 l.2
  have e2 := h.code u' (placeNo P.H 0) l.1 l.2
  rw [huu, e2] at e1
  change _ - (if c u' l then _ else _) = _ - (if c u l then _ else _) at e1
  cases h1 : c u l <;> cases h2 : c u' l <;> simp only [h1, h2, if_true, Bool.false_eq_true, if_false] at e1 ⊢ <;> (exfalso; linarith)

set_option maxHeartbeats 1000000 in

theorem ev_preX_frame : StandardLattice.SiegelMassRatioCM → Ev fun K => ∀ B : Pre, K.Over B → Nonempty (PreX B) ∧ Nonempty (Fr B) := by
  intro h2b
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ⟨0, fun cD hcD => ?_⟩⟩⟩
  obtain ⟨c2, hw⟩ := window_lower h2b eps C h0 h1 hC cD hcD
  refine ⟨max c2 0, fun ch hch => ?_⟩
  have hch0 : 0 ≤ ch := le_trans (le_max_right _ _) hch
  obtain ⟨x1, hx1⟩ := hw ch (le_trans (le_max_left _ _) hch)
  obtain ⟨x2, hx2⟩ := places_ok eps C cD ch h0 h1 hC hcD hch0
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 406 1 h0 one_pos
  refine ⟨max (max x1 x2) (max x3 (max x4 10)), ?_⟩
  rintro ⟨s, C', cD', ch', P, q1, a, b, c, std, ok, Lv, hdu, hDs, hG⟩ rfl rfl rfl he hx B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
  simp only [max_le_iff] at he hx
  obtain ⟨⟨y1, y2⟩, y3, y4, y5⟩ := hx
  have hev : (Pre.ofCh P Lv sp hT hY hA hV hz).EvenExp := (ok.hc P.u₀).2.2.2
  refine ⟨?_, Pre.nonempty_hframe _ hev⟩
  have hlow := hx1 s P q1 a b c Lv.duStar Lv.Dstar he y1 ok hdu (hDs ▸ (GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P).2)
  have hpl := hx2 s P q1 a b c he y2 ok
  obtain ⟨hf, -, hr, hkr, -, -, hL1, -, -, -, -, -, -, -, hN, -⟩ := hx3 s P.R he y3 ok.rank
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hb0 : 0 < s.b := Real.exp_pos _
  have hk3 := P.R.m_add_three_le_k
  have hm2 := P.R.two_le_m
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (P.R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hN' : (P.R.N P.R.m : ℝ) ≤ s.x ^ 402 := by rw [← pw]; exact_mod_cast hN
  have hb' : s.x ^ 406 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have hone : 1 ≤ s.x := by linarith
  have hz1 : 10 * s.x ^ 405 ≤ s.b := by
    calc 10 * s.x ^ 405 ≤ s.x * s.x ^ 405 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 406 := by ring
      _ ≤ s.b := hb'
  have hfN : (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 405 := by
    calc (P.R.f : ℝ) * P.R.N P.R.m ≤ s.x ^ 3 * s.x ^ 402 := mul_le_mul hf' hN' (by positivity) (by positivity)
      _ = s.x ^ 405 := by ring
  have hN2 : (P.R.N P.R.m : ℝ) ≤ s.x ^ 405 := hN'.trans (pow_le_pow_right₀ hone (by norm_num))
  have hx2' : 10 * s.x ≤ s.x ^ 405 := by
    calc 10 * s.x ≤ s.x ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ hone (by norm_num)
  generalize s.x ^ 405 = z at hz1 hfN hN2 hx2'
  have hkN : (P.R.k : ℝ) ≤ P.R.N P.R.m := by
    have : P.R.k ≤ P.R.N P.R.m := Nat.le_add_right _ _
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hbb : 1000 * s.b ≤ s.b * s.b := by nlinarith
  have hxb : 100 * (s.x * s.b) ≤ s.b * s.b := by nlinarith
  choose πg g1 g2 g3 using ok.gnorm
  refine ⟨{ piG := πg
            piG_K := g1
            piG_norm := g2
            piG_cong := fun i => Ideal.mem_span_singleton.1 (g3 i)
            piT := Lv.piT
            piT_K := Lv.piT_K
            piT_norm := Lv.piT_norm
            piT_cong := fun u => Ideal.mem_span_singleton.1 (Lv.piT_cong u)
            pde_split := ok.arith.2.2.1
            ccK_top := P.ccK_top
            e_even := hev
            hcW_inj := hcW_injective ok
            a := s.b * s.b / 5
            g_big := fun i => ?_
            T_gt := fun u => ?_
            a_gt := ?_
            spread_le := fun u j hj τ => ?_ }⟩
  · show 2 * P.R.f * P.R.k < P.H.g i - 1
    have b1 : 1 ≤ s.b := by linarith
    have c1 : s.b ≤ (P.H.g i : ℝ) :=
      calc s.b ≤ (P.R.k : ℝ) * s.b := le_mul_of_one_le_left hb0.le hk1
        _ ≤ ((P.R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 b1) (by norm_num)
        _ ≤ _ := (ok.val.2.2.2.2.1 i).1
    have c2 : (P.R.f : ℝ) * P.R.k ≤ P.R.f * P.R.N P.R.m := mul_le_mul_of_nonneg_left hkN (by positivity)
    have c3 : ((2 * P.R.f * P.R.k + 1 : ℕ) : ℝ) < P.H.g i := by
      push_cast
      nlinarith
    have c4 : 2 * P.R.f * P.R.k + 1 < P.H.g i := by exact_mod_cast c3
    omega
  · show 4 * (s.b * s.b / 5) < (Lv.T u : ℝ)
    have w := (Lv.T_win u).1
    rw [hG] at w
    have hT0 : 0 < (Lv.Dstar / Lv.duStar u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C' s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)) := by
      have : (0 : ℝ) < Lv.duStar u := by exact_mod_cast Lv.duStar_pos u
      have := Lv.Dstar_pos
      have : 0 < GamS C' s P.R := Real.exp_pos _
      positivity
    have c1 := ((Real.le_log_iff_exp_le hT0).1 (hlow u)).trans w
    have c2 : s.b * s.b ≤ Real.exp (P.R.m * s.L) := by
      unfold Scale.b
      rw [← Real.exp_add]
      have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm2
      have := mul_le_mul_of_nonneg_right this (by linarith : 0 ≤ s.L)
      exact Real.exp_le_exp.2 (by linarith)
    have := mul_pos hb0 hb0
    linarith
  · show ((2 * P.R.f * P.R.N P.R.m + 1 : ℕ) : ℝ) < 4 * (s.b * s.b / 5)
    push_cast
    nlinarith
  · show (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤ 2 * (s.b * s.b / 5)
    have hk0 : 0 < P.R.k := by omega
    have hm0 : 0 < P.R.m := by omega
    have hm1 : P.R.m - 1 < P.R.m := by omega
    have c1 := spread_lamOf_le (P.hcW u τ) j hj hk0 hm1
    have c2 : (((lamOf (P.hcW u τ) j).spread : ℤ) : ℝ) ≤
        (((P.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) + P.R.N P.R.m := by
      exact_mod_cast c1
    obtain ⟨⟨p1, -, -, -, p5, -, -, p8, p9⟩, p10⟩ := hpl u τ
    have p1' := (p1 0 (by omega)).2
    rw [seqOf_lt _ hk0] at p5
    rw [seqOf_lt _ hm0] at p8
    rw [seqOf_lt _ hm1] at p9
    obtain ⟨-, -, ⟨b1, v3, -⟩, -⟩ := ok.hc u
    have d1 : (P.hcW u τ).b ⟨0, hm0⟩ ≤ (P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ := by
      rw [(v3 τ _).2, (v3 τ _).1, (v3 τ _).1]
      have : (0 : ℚ) ≤ ((P.R.m - 1 : ℕ) : ℚ) * (h0v s ch' : ℚ) + (h0v s ch' : ℚ) / 2 := by positivity
      simp only [Nat.cast_zero, zero_mul]
      linarith
    have d2 : (((P.hcW u τ).b ⟨0, hm0⟩ : ℚ) : ℝ) ≤ (((P.hcW u τ).e ⟨P.R.m - 1, hm1⟩ : ℚ) : ℝ) := by exact_mod_cast d1
    have d3 : (P.R.k : ℝ) * (4 * (Delv s cD' : ℝ)) ≤ 2 * s.b := by
      refine p8.trans ?_
      rw [div_le_iff₀ hx0]
      nlinarith
    have ea : s.a = s.x * s.b := rfl
    have hxb0 : 0 ≤ s.x * s.b := by positivity
    rcases p5 with ⟨q, -⟩ | ⟨-, q, -⟩ <;> linarith

end GlobalTheory.Mem.Top

end
