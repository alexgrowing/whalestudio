import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CosetExpUnique
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowGat
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRecordOverChoices
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

namespace GlobalTheory.Diag.PG.Model0

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem scale_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  positivity

theorem duWin_of_data {D : D7} {C0 : ℝ} (h : StandingNumericalData D C0) : DuWin D C0 := h.2.2.2.2.2.2.2.2.2.1

theorem duWin_zero_iff (D : D7) : DuWin D 0 ↔ ∀ u, D.duS u = 0 := by
  unfold DuWin
  simp

theorem duWin_forces {D : D7} {C0 : ℝ} (h : DuWin D C0) (h0 : C0 ≠ 0) : 1 ≤ C0 ∧ ∀ u, D.duS u ≠ 0 := by
  obtain ⟨a, b⟩ := h D.u₀
  have hp := scale_pos D D.u₀
  have hd : (0 : ℝ) ≤ D.duS D.u₀ := Nat.cast_nonneg _
  have hC : 0 < C0 := by
    rcases lt_or_gt_of_ne h0 with hc | hc
    · nlinarith
    · exact hc
  refine ⟨?_, fun u hu => ?_⟩
  · rw [div_le_iff₀ hC] at a
    by_contra hc
    have h1 : C0 < 1 := not_le.1 hc
    have h2 : (D.duS D.u₀ : ℝ) * C0 ≤ (D.mem D.u₀).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0 * C0 :=
      mul_le_mul_of_nonneg_right b hC.le
    have h3 : C0 * C0 < 1 := by nlinarith
    nlinarith
  · have a := (h u).1
    rw [hu, Nat.cast_zero] at a
    exact absurd a (not_le.2 (div_pos (scale_pos D u) hC))

theorem duWin_three (D : D7)
    (hr : ∀ u, (D.duS u : ℝ) = ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) : DuWin D 3 := by
  intro u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD := (D.mem u).A.Dstar_pos
  have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hN : (0 : ℝ) < (D.R.f : ℝ) * D.R.k := by positivity
  obtain ⟨w1, w2⟩ := D.T_win u
  set T : ℝ := ((D.mem u).A.T : ℝ) with hT
  set S : ℝ := (D.mem u).A.Tstar with hS
  have hS0 : 0 < S := by rw [hS]; unfold ColumnsAtT.Tstar ColumnsAtT.Xu; positivity
  have hT2 : (2 : ℝ) ≤ T := by rw [hT]; exact_mod_cast (D.mem u).A.T_prime.two_le
  have key : (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar = (D.mem u).A.duStar * S ^ (D.R.f * D.R.k) := by
    rw [hS, ← D.Dstar_eq u]
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hG.le]
    push_cast
    rw [one_div_mul_cancel hN.ne', div_mul_cancel₀ _ hN.ne', Real.rpow_one, ← Real.rpow_intCast]
    push_cast
    field_simp
  have hTk : 2 * (D.R.f : ℝ) ≤ T ^ D.R.k := by
    have a : 2 * D.R.k ≤ 2 ^ D.R.k := by
      obtain ⟨j, hj⟩ : ∃ j, D.R.k = j + 1 := ⟨D.R.k - 1, by omega⟩
      rw [hj, pow_succ]
      have := Nat.lt_two_pow_self (n := j)
      omega
    have b : (2 : ℝ) * D.R.f ≤ 2 ^ D.R.k := by exact_mod_cast (by omega : 2 * D.R.f ≤ 2 ^ D.R.k)
    exact b.trans (pow_le_pow_left₀ (by norm_num) hT2 _)
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hTp : 0 < T ^ D.R.k := by positivity
  rw [key, hr u]
  constructor
  · have a : S ^ (D.R.f * D.R.k) ≤ (T ^ D.R.k) ^ D.R.f := by
      rw [← pow_mul, mul_comm D.R.k]; exact pow_le_pow_left₀ hS0.le w1 _
    have hq : 1 / T ^ D.R.k ≤ 1 := by rw [div_le_one hTp]; linarith
    have b := one_add_mul_le_pow (a := -(1 / T ^ D.R.k)) (by linarith [show 0 ≤ 1 / T ^ D.R.k by positivity]) D.R.f
    have c : (D.R.f : ℝ) * (1 / T ^ D.R.k) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hTp]; linarith
    have e : (T ^ D.R.k - 1) ^ D.R.f = (T ^ D.R.k) ^ D.R.f * (1 + -(1 / T ^ D.R.k)) ^ D.R.f := by
      rw [← mul_pow]; congr 1; field_simp; ring
    have g : (1 : ℝ) / 2 ≤ (1 + -(1 / T ^ D.R.k)) ^ D.R.f := by linarith
    have hp : 0 < (T ^ D.R.k) ^ D.R.f := by positivity
    have : S ^ (D.R.f * D.R.k) / 3 ≤ (T ^ D.R.k - 1) ^ D.R.f := by rw [e]; nlinarith
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hd.le
  · have a : (T ^ D.R.k - 1) ^ D.R.f ≤ T ^ (D.R.f * D.R.k) := by
      rw [mul_comm, pow_mul]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have b : T ^ (D.R.f * D.R.k) ≤ ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * S) ^ (D.R.f * D.R.k) :=
      pow_le_pow_left₀ (by linarith) w2 _
    have c : (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) ≤ 3 := by
      have c1 : 1 + 1 / ((D.R.f : ℝ) * D.R.k) ≤ Real.exp (1 / ((D.R.f : ℝ) * D.R.k)) := by
        linarith [Real.add_one_le_exp (1 / ((D.R.f : ℝ) * D.R.k))]
      refine (pow_le_pow_left₀ (by positivity) c1 _).trans ?_
      rw [← Real.exp_nat_mul]
      push_cast
      rw [mul_one_div_cancel hN.ne']
      linarith [Real.exp_one_lt_d9]
    rw [mul_pow] at b
    have hp : 0 < S ^ (D.R.f * D.R.k) := by positivity
    have : (T ^ D.R.k - 1) ^ D.R.f ≤ S ^ (D.R.f * D.R.k) * 3 := by nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this hd.le

section Rec

open Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ

abbrev pkg (N : ℕ) : ClsPkg where
  cls := fun _ => Fin (N + 1)
  clsFin := fun _ => inferInstance
  stab := fun _ _ => Unit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := 1
  DGam_pos := one_pos
  dvd := fun _ _ => by simp

set_option maxHeartbeats 1600000 in

def recd (N : ℕ) : D7 :=
  letI := H0.cmStar
  hostLevelRecord H0 (W := Unit) () (fun _ _ => hc0) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => pkg N) (fun _ => T0) (dstarOf T0) (dstarOf_pos T0) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 T0) exampleHost_type_primes_split exampleHost_typeHypothesis (fun _ => examplePrime_mem_levelPrimes) (fun _ => examplePrime_ne_split_primes) (fun _ => π0O)
    (fun _ => π0_mem_K) (fun _ => π0_norm) (fun _ => π0_cong)
    (fun _ i _ => ((hostSpacesOfNorm H0 T0 (π0O : H0.E) π0_norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm H0 T0 (π0O : H0.E) π0_norm).X i).standardTuple_isLattice)
    (LocalGap.localGapOfRecord GlobalTheory.Mem.nonempty_record_of_locStage.some _)
    (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl_nonempty H0 exampleHost_typeHypothesis 5 (by norm_num) (by decide) (by decide)).some (fun _ => by norm_num [T0]) (fun _ _ => 0)
    (fun _ => ⊤)
    (localDataAtServedPlace' H0 (fun _ _ => hc0) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes H0 (fun _ _ => hc0) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

theorem recd_duS (N u) : (recd N).duS u = N + 1 :=
  (atTN_rank (fun _ : Tau2 R0 => hc0) (pkg N) T0 (dstarOf T0) (dstarOf_pos T0) 1 one_pos 2 one_lt_two).trans (by simp)

end Rec

theorem succ_pred_pow (T k f : ℕ) (hT : 2 ≤ T) (hk : 0 < k) :
    ∃ N : ℕ, ((N + 1 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) * ((T : ℝ) ^ k - 1) ^ f := by
  have a : 1 < T ^ k := Nat.one_lt_pow hk.ne' hT
  have b : 0 < (T ^ k - 1) ^ f := pow_pos (by omega) _
  refine ⟨(T ^ k - 1) ^ f - 1, ?_⟩
  rw [Nat.sub_add_cancel b]
  push_cast [Nat.cast_sub a.le]
  ring

open Formalism.BasicNotions.Examples₂ in

theorem duWin_nontrivial : (∃ D : D7, DuWin D 3 ∧ ∀ u, D.duS u ≠ 0) ∧ ∃ D : D7, ¬ DuWin D 3 ∧ ∀ u, D.duS u ≠ 0 := by
  obtain ⟨N, hN⟩ := succ_pred_pow T0 R0.k R0.f examplePrime_prime.two_le (by decide)
  have h : DuWin (recd N) 3 := duWin_three _ fun u => by rw [recd_duS]; exact hN
  refine ⟨⟨_, h, (duWin_forces h (by norm_num)).2⟩, recd (9 * N + 9), fun h' => ?_, fun u => by
    rw [recd_duS]; omega⟩
  have a := (h ()).1
  have b := (h' ()).2
  rw [recd_duS N ()] at a
  rw [recd_duS (9 * N + 9) ()] at b
  have e : ((recd (9 * N + 9)).mem ()).A.GamP ^ (-2 : ℤ) * (recd (9 * N + 9)).what₂.Dstar =
      ((recd N).mem ()).A.GamP ^ (-2 : ℤ) * (recd N).what₂.Dstar := rfl
  rw [e] at b
  push_cast at a b
  linarith

theorem two_le_rd {R : Ranks} (H : Host R) : 2 ≤ H.rdE := UpperTheory.Ram.Rd.two_le_rdE H

theorem logrd_le {D : D7} (L : SizeData₂ D) (SzN : SizeN L) (SzQ : SizeQD L) (h2 : 2 ≤ XX L) (h3 : 5 / szTh L ≤ XX L) :
    Real.log D.host.rdE ≤ L.sc.x ^ (L.sc.eps / 2) := by
  obtain ⟨-, -, q2, -, d2, -⟩ := SzQ
  have a := UpperTheory.Ram.Rd.log_rdE_le D.host
  have b := logn_le L SzN
  have c := logx_le L
  have e21 : L.sc.x ^ (L.sc.eps / 5 + szTh L) = XX L ^ 21 := by
    rw [← xpow_nat L 21]; congr 1; unfold szTh; push_cast; ring
  have e50 : L.sc.x ^ (L.sc.eps / 2) = XX L ^ 50 := by
    rw [← xpow_nat L 50]; congr 1; unfold szTh; push_cast; ring
  rw [e21] at q2 d2
  rw [e50]
  have hth := th_pos L
  have k1 : 5 * (XX L / szTh L) ≤ XX L ^ 2 := by
    have : 5 * (XX L / szTh L) = 5 / szTh L * XX L := by ring
    rw [this, sq]; exact mul_le_mul_of_nonneg_right h3 (by linarith)
  have k0 : 0 ≤ XX L / szTh L := by positivity
  have k2 : XX L ^ 2 ≤ XX L ^ 21 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have k3 : 1 ≤ XX L ^ 21 := one_le_pow₀ (by linarith)
  have k4 : 4 ≤ XX L ^ 29 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) h2 29)
  have k5 : XX L ^ 50 = XX L ^ 21 * XX L ^ 29 := by ring
  nlinarith

theorem globalRows_of_sizeData {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (Sz : SizesAt L) (h2 : 2 ≤ XX L)
    (h3 : 5 / szTh L ≤ XX L) (CD : ℝ) (h0 : 0 < CD) (hC : CD ≤ P.CCount) :
    Glob0 D L.sc.x L.sc.eps CD (P.CYL + 1) := by
  obtain ⟨SzN, SzM, SzK, SzKR, -, -, SzQ, -, -, -, -, -, -, -, SzNo, -, SzD, -⟩ := Sz
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hS := Sc_eq' L
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, Real.log_le_log (by norm_num) (two_le_rd _), logrd_le L SzN SzQ h2 h3, count_power_le_discriminant L P CD h0 hC, ?_⟩,
    type_prime_size_bounds L P, fun τ j h => ?_, fun τ i => ?_, fun τ ht => ?_, two_le_rd _⟩
  · have a := SzM.1
    rw [sqrt_xd L, ← Real.rpow_add hx] at a
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_) a
    unfold szTh; linarith
  · exact_mod_cast hyp3 L SzN SzM
  · exact_mod_cast D.R.f_le_k
  · have a := SzKR.1
    have b : L.sc.x ^ (L.sc.eps / 2) ≤ L.sc.x ^ L.sc.eps := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have c : 1 ≤ L.sc.x ^ szTh L := (one_lt_XX L).le
    have e : L.sc.L = L.sc.x ^ L.sc.eps := rfl
    rw [e] at a
    refine le_trans ?_ a
    calc _ = 1 * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps / 2) := by ring
      _ ≤ _ := by gcongr
  · refine SzK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    unfold szTh; linarith
  · have b : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 2) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have c : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
    linarith [P.logDel]
  · exact le_trans SzNo.2.2.1 (P.nodes_gap τ j h).1
  · rw [← hS]; exact L.cloud_v τ i
  · have hn : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := fun h => ht ((isTop_iff τ).2 h)
    have a := (L.cloud_gap τ (by omega) hn).1
    have b := P.cloud_place_bound τ (by omega) hn
    have c := P.uk_extreme τ (by omega) hn
    push_cast at a b
    unfold uFirst vFirst uLast vLast
    refine ⟨by linarith, by linarith, ?_⟩
    rw [c]; push_cast; ring

open Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RunJoin GlobalTheory.Mem GlobalTheory.EX.OB in

theorem exists_glob0_of_zeroFreeRegion (p1 : GlobalTheory.Mem.An.ExplZeta) (p2 : GlobalTheory.Mem.An.ExplChi) (p3 : GlobalTheory.Mem.An.LogDerOne)
    (p4 : GlobalTheory.Mem.An.ZeroCount) (p5 : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (p6 : GlobalTheory.Mem.An.TZRat) (p7 : GlobalTheory.Mem.An.PageThm)
    (p8 : GlobalTheory.Mem.An.Jutila) (p9 : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) (hR : GlobalTheory.NT.RayField)
    (eps CD x : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hCD : 0 < CD) :
    ∃ (y : ℝ) (D : D7), x ≤ y ∧ Glob0 D y eps CD 10 ∧ (∃ τ, Top D τ) ∧ ∃ τ, ¬ Top D τ := by
  have hH := DC.hostExQ_of_hostEx (smallPrimeOne_of_tzRat p6) (hostEx_of_zeroFreeRegion p1 p2 p3 p4 p5 p6 p7 p8 p9)
  have hLP := (normPrimes_and_levelPrime p9).2
  obtain ⟨CT2, C8, C5, c6, Cb, hC8, -, -, -, hK⟩ := exists_chGood_unb hH _ he he52
  obtain ⟨C, hStd, hCT2, hCp, hL, -⟩ := exists_std_large ⟨0, 0, fun _ => 0, fun _ => CD⟩
    ⟨0, 0, fun _ => 0, fun _ => 0⟩ CT2 C8 hC8
  have hCC : CD ≤ C.P.CCount := hL.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨c1, hN⟩ := szRow_numAt _ he he52 C hStd
  obtain ⟨c2, hN⟩ := hN (max c1 0) (le_max_left _ _)
  obtain ⟨x1, hN⟩ := hN (max c2 402) (le_max_left _ _)
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP _ 1 C he he52 one_pos hStd
  obtain ⟨x4, h4⟩ := exists_record_over_choices hR _ (max c1 0) (max c2 402) C he he52 hStd (le_max_right _ _) (le_max_right _ _)
  obtain ⟨s, hs, hsy, hK⟩ := hK C hStd hCT2 hCp (max c1 0) (le_max_right _ _) (max c2 402) (le_max_right _ _)
    (max x1 (max x3 (max x4 (max x ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)))))
  obtain ⟨y, hy⟩ : ∃ y, s.x = y := ⟨_, rfl⟩
  have hy1 : x1 ≤ y := hy ▸ (le_max_left _ _).trans hsy
  have hy3 : x3 ≤ s.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hsy
  have hy4 : x4 ≤ s.x := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hsy
  have hyx : x ≤ y :=
    hy ▸ ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hsy
  have hyP : (max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹ ≤ y :=
    hy ▸ ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hsy
  obtain ⟨P, a, b, c, hP, -⟩ := hK 0
  have hfk : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have h1 := P.R.m_add_three_le_k
    have h2 : 0 < P.R.f := by unfold Ranks.f Ranks.n; positivity
    have h3 : 0 < P.R.k := by omega
    positivity
  obtain ⟨Ds, hDs, hlog⟩ := exists_window_start _ (1 * P.R.m * s.L) (GamS C s P.R) hfk (Real.exp_pos _)
  obtain ⟨Lv, -, -, l3⟩ := h3 _ _ s P _ a b c (fun _ => 1) Ds hs hy3 hP.ok (fun _ => one_pos) hDs (fun _ => hlog)
  obtain ⟨D, -, -, -, hA, L, hsc, hV⟩ := h4 s P _ a b c Lv hs hy4 hP.ok l3
  have hsx : L.sc.x = y := by rw [hsc, hy]
  have hse : L.sc.eps = eps := by rw [hsc, hs]
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (hy1.trans hsx.ge) hV hA
  have e1 : N.params.CCount = C.P.CCount := by
    have := congrArg (fun l : List ℝ => l.getD 12 0) N.params_K
    exact this
  have e2 : N.params.CYL = C.P.CYL := by
    have := congrArg (fun l : List ℝ => l.getD 19 0) N.params_K
    exact this
  have hX : max 2 (5 / (eps / 100)) ≤ XX L := by
    unfold XX szTh
    rw [hsx, hse]
    have h0 : (0 : ℝ) ≤ max 2 (5 / (eps / 100)) := le_trans (by norm_num) (le_max_left _ _)
    have hp : 0 < eps / 100 := by positivity
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hyP hp.le
    rwa [Real.rpow_inv_rpow h0 hp.ne'] at this
  have G := globalRows_of_sizeData L N.params N.sizes ((le_max_left _ _).trans hX)
    (by unfold szTh; rw [hse]; exact (le_max_right _ _).trans hX) CD hCD (e1 ▸ hCC)
  rw [hsx, hse, e2, hStd.2.2.2.2.2.1, show (9 : ℝ) + 1 = 10 by norm_num] at G
  refine ⟨y, D, hyx, G, Model.exists_top D ?_, Model.exists_not_top D⟩
  have t1 := hV.host.2.1.1
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hd : 0 < L.sc.delta1 := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have : (0 : ℝ) < D.host.TT.card := lt_of_lt_of_le (by positivity) t1
  exact Finset.card_pos.1 (by exact_mod_cast this)

theorem one_lt_of_global_data {D : D7} {x eps CD Cg : ℝ} (G : Glob0 D x eps CD Cg) : 1 < x := by
  have h := G.nums.k_hi
  have hk : (5 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  by_contra hc
  have : x ^ 5 ≤ 1 ^ 5 := (Odd.strictMono_pow (by decide : Odd 5)).monotone (not_lt.1 hc)
  linarith

theorem not_glob0_small (x eps CD Cg : ℝ) : ¬ Glob0 (recd 0) x eps CD Cg := fun G => by
  have h : ((2 : ℕ) : ℝ) ^ 4 ≤ ((8 : ℕ) : ℝ) := G.nums.mf
  norm_num at h

end GlobalTheory.Diag.PG.Model0

end
