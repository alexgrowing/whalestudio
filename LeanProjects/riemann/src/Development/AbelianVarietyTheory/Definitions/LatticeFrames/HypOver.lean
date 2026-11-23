import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RankConditionRankOneIffEqZero
import Formalism.SharpRestriction.FamCore
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowGat
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage

noncomputable section

namespace GlobalTheory.Core.RkFamModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ GlobalTheory.Core.Rk NumberField Module

theorem rk_share {D : D7} {u : D.what₂.Word} (h : RK D u) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) : RKShare ρ D u := by
  have h1 : dU D u < 2 * rkC (D.mem u).C (D.mem u).A (D.mem u).P := h
  refine ⟨by omega, ?_⟩
  have h2 : (dU D u : ℝ) < 2 * (rkC (D.mem u).C (D.mem u).A (D.mem u).P : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ (dU D u : ℝ) := by positivity
  nlinarith

theorem someAt_mono (F : Pts) {Q Q' : ℝ → ∀ D : D7, D.what₂.Word → Prop} (x₁ : ℝ)
    (hq : ∀ x, x₁ ≤ x → ∀ i u, Q x (F.D x i) u → Q' x (F.D x i) u) (h : F.SomeAt Q) : F.SomeAt Q' := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨max x₀ x₁, fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2, u, h3⟩ := h x (le_of_max_le_left hx) i₀ u₀ hu
  exact ⟨i, h1, h2, u, hq x (le_of_max_le_right hx) i u h3⟩

theorem win_of_room (F : Pts) (ε : ℝ) (h : F.RKRoom ε) : F.RKWin := by
  obtain ⟨CR, CT, h⟩ := h
  exact someAt_mono F 0 (fun _ _ _ _ h => h.2) h

theorem weak_of_room (F : Pts) {ε : ℝ} (hε : 0 < ε) (h : F.RKRoom ε) : F.RKWeak ε := by
  obtain ⟨CR, CT, h⟩ := h
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by linarith : 0 < 12 * ε)).eventually_ge_atTop (max CR 2)).and (Filter.eventually_gt_atTop (0 : ℝ)))
  refine ⟨CT, someAt_mono F x₁ (fun x hx i u h => ?_) h⟩
  obtain ⟨h1, h0⟩ := hx₁ x hx
  have e : x ^ (13 * ε) = x ^ (12 * ε) * x ^ ε := by rw [← Real.rpow_add h0]; ring_nf
  have hp : 0 < x ^ ε := Real.rpow_pos_of_pos h0 _
  refine ⟨⟨?_, h.1.2⟩, rk_share h.2 ?_⟩
  · have := h.1.1
    have h2 : CR * x ^ ε ≤ x ^ (12 * ε) * x ^ ε := mul_le_mul_of_nonneg_right (le_of_max_le_left h1) hp.le
    linarith
  · rw [Real.rpow_neg h0.le, one_div]
    exact inv_anti₀ (by norm_num) (le_of_max_le_right h1)

theorem xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem fk_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem log_tstar (D : D7) (u : D.what₂.Word) : Real.log (D.mem u).A.Tstar =
    Real.log (D.mem u).A.Xu - 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

theorem log_T_lt (D : D7) (u : D.what₂.Word) :
    Real.log ((D.mem u).A.T : ℝ) < Real.log (D.mem u).A.Xu + 1 / ((D.R.f : ℝ) * D.R.k) := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := fk_pos D.R
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hT (D.T_win u).2
  rw [Real.log_mul (by positivity) hs.ne', log_tstar] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : 0 < 2 / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP :=
    mul_pos (by positivity) (Real.log_pos (D.mem u).A.one_lt_gammaP)
  linarith

theorem le_log_alt {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    Real.log (D.mem u).A.Xu - 2 * L.CGam * (D.R.m : ℝ) ^ 5 / D.R.k * L.sc.L ≤ Real.log ((D.mem u).A.T : ℝ) := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (xu_pos D u) (Real.rpow_pos_of_pos hG _)
  have h1 := Real.log_le_log hs (D.T_win u).1
  rw [log_tstar, L.Gam_eq u] at h1
  have hf := fk_pos D.R
  have hf1 : (D.R.f : ℝ) ≠ 0 := left_ne_zero_of_mul hf.ne'
  have hk1 : (D.R.k : ℝ) ≠ 0 := right_ne_zero_of_mul hf.ne'
  have e : 2 / ((D.R.f : ℝ) * D.R.k) * (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L) =
      2 * L.CGam * (D.R.m : ℝ) ^ 5 / D.R.k * L.sc.L := by field_simp
  linarith

theorem sameTops_iff {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hk : D.R.k = D'.R.k) :
    SameTops D D' ↔ ∀ (t : D.host.TT) (t' : D'.host.TT),
      (t : D.R.A).val = (t' : D'.R.A).val → L.aT t = L'.aT t' ∧ L.bT t = L'.bT t' := by
  have h : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have h' : 0 < D'.R.k := by omega
  have hkr : (D.R.k : ℝ) = D'.R.k := by exact_mod_cast hk
  constructor
  · intro H t t' ht
    have e1 : (D.eTau (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) : D.R.GG) = D.R.tau1 t := by
      rw [Equiv.apply_symm_apply]
    have e2 : (D'.eTau (D'.eTau.symm ⟨D'.R.tau1 t', (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) : D'.R.GG) =
        D'.R.tau1 t' := by rw [Equiv.apply_symm_apply]
    obtain ⟨a, b⟩ := H _ _ t t' h h' e1 e2 ht
    obtain ⟨c1, c2⟩ := L.top_u _ t h e1
    obtain ⟨d1, d2⟩ := L'.top_u _ t' h' e2
    rw [a, d1] at c1
    rw [b, d2] at c2
    constructor
    · exact_mod_cast (by linarith : (L.aT t : ℝ) = L'.aT t')
    · exact_mod_cast (by linarith : (L.bT t : ℝ) = L'.bT t')
  · intro H τ τ' t t' h h' e1 e2 ht
    obtain ⟨a, b⟩ := H t t' ht
    obtain ⟨c1, c2⟩ := L.top_u _ t h e1
    obtain ⟨d1, d2⟩ := L'.top_u _ t' h' e2
    rw [a, hkr, ← d1] at c1
    rw [b, hkr, ← d2] at c2
    exact ⟨by exact_mod_cast c1, by exact_mod_cast c2⟩

def ptsOf {ε : ℝ} (F : FamCore ε) : Pts := Pts.ofFam F

theorem win_of_all {ε : ℝ} (F : FamCore ε) (h : (ptsOf F).RKAll) : (ptsOf F).RKWin := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨max x₀ (F.x1 + 1), fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2⟩ := F.coverS x (by have := le_of_max_le_right hx; linarith) i₀ u₀ hu
  exact ⟨i, h1, (sameTops_iff (F.L x i) (F.L x i₀) (congrArg Ranks.k (F.R_eq x i i₀))).2 h2, h x (le_of_max_le_left hx) i⟩

theorem exists_of_win {ε : ℝ} (F : FamCore ε) (h : (ptsOf F).RKWin) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → x ∈ F.Win → ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), RK (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨x₀, fun x hx hw => ?_⟩
  obtain ⟨i₀⟩ := F.Ix_win x hw
  obtain ⟨i, -, -, u, hu⟩ := h x hx i₀ 0 (F.D x i₀).R.ord_pos
  exact ⟨i, u, hu⟩

abbrev Ht (t : R0.A) : Host R0 := { H0 with TT := Finset.univ, u0 := t }

def hcA (c : ℕ) : HCParam R0 :=
  { hc0 with
    u := fun i => hc0.u i + if i.1 = 0 then (c : ℚ) else 0
    u_gt_v := fun i => by
      have := hc0.u_gt_v i
      have h2 : (0 : ℚ) ≤ if i.1 = 0 then (c : ℚ) else 0 := by split_ifs <;> positivity
      dsimp only
      linarith
    v_gt_u := fun i => by simpa using hc0.v_gt_u i
    u_last_gt := fun h h' => by
      have := hc0.u_last_gt h h'
      have h2 : (0 : ℚ) ≤ if R0.k - 1 = 0 then (c : ℚ) else 0 := by split_ifs <;> positivity
      dsimp only
      linarith
    u_half := fun i => by
      obtain ⟨z, hz⟩ := hc0.u_half i
      by_cases h : i.1 = 0
      · exact ⟨z + c, by simp only [h, if_true, hz]; push_cast; ring⟩
      · exact ⟨z, by simp only [h, if_false, hz, add_zero]⟩ }

abbrev pkg (N : ℕ) : ClsPkg where
  cls := fun _ => Fin (N + 1)
  clsFin := fun _ => inferInstance
  stab := fun _ _ => Unit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := 1
  DGam_pos := one_pos
  dvd := fun _ _ => by simp

def perS (N : ℕ) (s : ℂ) : FK (Fin (N + 1)) →ₗ[ℂ] En 1 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun φ F => s * φ 0 () * F 0) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem tH (t : R0.A) : THyp (Ht t) := ⟨exampleHost_typeHypothesis.cond, exampleHost_typeHypothesis.bb, exampleHost_typeHypothesis.jac⟩

def gap (t : R0.A) : LocalGap (Ht t) := LocalGap.localGapOfRecord GlobalTheory.Mem.nonempty_record_of_locStage.some _

def lbl (t : R0.A) : Lbl (Ht t) := (lbl_nonempty (Ht t) (tH t) 5 (by norm_num) (by decide) (by decide)).some

set_option maxHeartbeats 1600000 in

def recd (t : R0.A) (c N : ℕ) (s : ℂ) : D7 :=
  letI := (Ht t).cmStar
  hostLevelRecord (Ht t) (W := Unit) () (fun _ _ => hcA c) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      simp only [hcA, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => pkg N) (fun _ => T0) (dstarOf T0) (dstarOf_pos T0) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 T0) exampleHost_type_primes_split (tH t) (fun _ => examplePrime_mem_levelPrimes) (fun _ => examplePrime_ne_split_primes) (fun _ => π0O)
    (fun _ => π0_mem_K) (fun _ => π0_norm) (fun _ => π0_cong)
    (fun _ i _ => ((hostSpacesOfNorm (Ht t) T0 (π0O : (Ht t).E) π0_norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm (Ht t) T0 (π0O : (Ht t).E) π0_norm).X i).standardTuple_isLattice)
    (gap t) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl t) (fun _ => by norm_num [T0]) (fun _ _ => perS N s) (fun _ => ⊤)
    (localDataAtServedPlace' (Ht t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes (Ht t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

section Rank

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (N : ℕ)

theorem colTo_one (j : ℕ) : colTo (chainN hc (pkg N)) j (fun _ _ => 1) = fun _ _ => ((N : ℂ) + 1) ^ j := by
  induction j with
  | zero => funext _ _; simp [colTo]
  | succ j ih =>
    show (chainN hc (pkg N)).K j (colTo (chainN hc (pkg N)) j (fun _ _ => 1)) = _
    rw [ih]
    funext c y
    have e : ∀ a : Fin (N + 1), (chainN hc (pkg N)).wt j a • (chainN hc (pkg N)).Kmap j a c (fun _ => ((N : ℂ) + 1) ^ j) =
        fun _ => ((N : ℂ) + 1) ^ j := fun a => by
      rw [chainN_Kmap hc (pkg N) j a c]
      simp [ColumnChain.wt]
    have e2 : (chainN hc (pkg N)).K j (fun _ _ => ((N : ℂ) + 1) ^ j) c = ∑ _a : Fin (N + 1), fun _ : Unit => ((N : ℂ) + 1) ^ j := by
      unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
      rw [Finset.sum_congr rfl fun a _ => e a]
    refine (congrFun e2 y).trans ?_
    simp [pow_succ]
    ring

variable (T : ℕ) [Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (hT : T ≠ 2) (s : ℂ)

theorem rk_le_one : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N s)) ≤ 1 := by
  unfold rkC
  refine (Submodule.finrank_le _).trans ?_
  show finrank ℂ (Module.Dual ℂ (En 1)) ≤ 1
  rw [Subspace.dual_finrank_eq]
  simp

theorem rk_zero : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N 0)) = 0 := by
  unfold rkC
  have : PhiC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
      (periodN hc (pkg N) (En 1) (perS N 0)) = 0 := by
    ext φ F
    show (0 : ℂ) * _ * _ = 0
    simp
  rw [this, LinearMap.range_zero, finrank_bot]

include hT in
theorem rk_one : rkC (chainN hc (pkg N)) (atTN hc (pkg N) T Dst hD 1 one_pos 2 one_lt_two)
    (periodN hc (pkg N) (En 1) (perS N 1)) = 1 := by
  refine le_antisymm (rk_le_one hc N T Dst hD 1) ?_
  unfold rkC
  haveI : FiniteDimensional ℂ (periodN hc (pkg N) (En 1) (perS N 1)).Mt := inferInstanceAs (FiniteDimensional ℂ (En 1))
  rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  intro h
  have h1 := LinearMap.congr_fun (LinearMap.congr_fun h ⟨fun _ _ => 1, by rw [atTN_Mram _ _ _ _ _ _ _ _ _ hT]; trivial⟩)
    (WithLp.toLp 2 fun _ => (1 : ℂ))
  have h2 : (1 : ℂ) * colTo (chainN hc (pkg N)) R.m (fun _ _ => 1) (0 : Fin (N + 1)) () * 1 = 0 := h1
  rw [colTo_one] at h2
  have h3 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  simp [h3] at h2

end Rank

theorem baseDegree_ne_two : T0 ≠ 2 := by norm_num [T0]

theorem recd_dU (t c N s u) : dU (recd t c N s) u = N + 1 :=
  (atTN_du (fun _ : Tau2 R0 => hcA c) (pkg N) T0 (dstarOf T0) (dstarOf_pos T0) 1 one_pos 2 one_lt_two baseDegree_ne_two).trans (by simp)

theorem columnRank_eq_one_of_rankOne (t c N u) : rkC ((recd t c N 1).mem u).C ((recd t c N 1).mem u).A ((recd t c N 1).mem u).P = 1 :=
  rk_one (fun _ : Tau2 R0 => hcA c) N T0 (dstarOf T0) (dstarOf_pos T0) baseDegree_ne_two

theorem columnRank_eq_zero_of_rankZero (t c N u) : rkC ((recd t c N 0).mem u).C ((recd t c N 0).mem u).A ((recd t c N 0).mem u).P = 0 :=
  rk_zero (fun _ : Tau2 R0 => hcA c) N T0 (dstarOf T0) (dstarOf_pos T0)

theorem rankCondition_rankOne_iff_eq_zero (t c N u) : RK (recd t c N 1) u ↔ N = 0 := by
  show dU _ u < 2 * _ ↔ _
  rw [recd_dU, columnRank_eq_one_of_rankOne]; omega

theorem not_rankCondition_rankZero (t c N u) : ¬ RK (recd t c N 0) u := by
  show ¬ dU _ u < 2 * _
  rw [recd_dU, columnRank_eq_zero_of_rankZero]; omega

theorem recd_share (t c N u) (ρ : ℝ) : RKShare ρ (recd t c N 1) u ↔ ρ * ((N : ℝ) + 1) ≤ 1 := by
  unfold RKShare
  rw [recd_dU, columnRank_eq_one_of_rankOne]
  simp

theorem recd_sameTops (t c N s t' c' N' s') : SameTops (recd t c N s) (recd t' c' N' s') ↔ c = c' := by
  constructor
  · intro H
    have := (H ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩ ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩
      ⟨(0 : R0.A), Finset.mem_univ _⟩ ⟨(0 : R0.A), Finset.mem_univ _⟩
      (show 0 < R0.k by decide) (show 0 < R0.k by decide) rfl rfl rfl).1
    have h2 : hc0.u ⟨0, by decide⟩ + (c : ℚ) = hc0.u ⟨0, by decide⟩ + (c' : ℚ) := this
    exact_mod_cast add_left_cancel h2
  · rintro rfl τ τ' _ _ h h' _ _ _
    exact ⟨rfl, rfl⟩

theorem val_cast (u₀ : ℕ) (h : u₀ < R0.n) : (R0.ofNat u₀).val = u₀ := R0.val_ofNat_of_lt h

theorem tIn_ev (D : R0.A → D7) (hm : ∀ t, (D t).R.m = 2) (v : ∀ t, (D t).what₂.Word) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ CR CT : ℝ, ∀ x, 1 ≤ x → ∀ t, TIn (D t) (v t) (CR * x ^ ε) (CT * (D t).R.m * x ^ ε) := by
  obtain ⟨a, ha⟩ := (Set.finite_range fun t => |Real.log ((D t).mem (v t)).A.Xu| + |Real.log (((D t).mem (v t)).A.T : ℝ)|).bddAbove
  refine ⟨a, a, fun x hx t => ?_⟩
  have h1 := ha ⟨t, rfl⟩
  have h2 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε
  have h3 := le_abs_self (Real.log ((D t).mem (v t)).A.Xu)
  have h4 := le_abs_self (Real.log (((D t).mem (v t)).A.T : ℝ))
  have h5 := neg_abs_le (Real.log (((D t).mem (v t)).A.T : ℝ))
  have h6 := abs_nonneg (Real.log ((D t).mem (v t)).A.Xu)
  have h7 := abs_nonneg (Real.log (((D t).mem (v t)).A.T : ℝ))
  dsimp only at h1
  have h8 : a ≤ a * x ^ ε := le_mul_of_one_le_right (by linarith) h2
  refine ⟨by linarith, ?_⟩
  rw [hm]
  push_cast
  nlinarith

end GlobalTheory.Core.RkFamModel

namespace GlobalTheory.Core.RkOverModel

open Formalism.BasicNotions GlobalTheory.Core.Rk GlobalTheory.Core.Rk.FamInh

theorem sameWord_symm {D D' : D7} {u : D.what₂.Word} {u' : D'.what₂.Word} (h : SameWord D u D' u') : SameWord D' u' D u :=
  ⟨h.host.symm, h.unitVector_val_eq.symm, fun τ' τ e => (h.hc_eq τ τ' e.symm).symm⟩

theorem sameWord_trans {D D' D'' : D7} {u : D.what₂.Word} {u' : D'.what₂.Word} {u'' : D''.what₂.Word}
    (h : SameWord D u D' u') (h' : SameWord D' u' D'' u'') : SameWord D u D'' u'' := by
  refine ⟨h.host.trans h'.host, h.unitVector_val_eq.trans h'.unitVector_val_eq, fun τ τ'' e => ?_⟩
  obtain ⟨τ', e1, e2⟩ := h.exists_place τ
  exact e2.trans (h'.hc_eq τ' τ'' (e1.symm.trans e))

theorem sameTops_symm {D D' : D7} (h : SameTops D D') : SameTops D' D := fun τ' τ t' t k' k e' e ht =>
  ⟨(h τ τ' t t' k k' e e' ht.symm).1.symm, (h τ τ' t t' k k' e e' ht.symm).2.symm⟩

theorem sameTops_trans {D D' D'' : D7} (hh : SameHost D D') (h : SameTops D D') (h' : SameTops D' D'') : SameTops D D'' := by
  intro τ τ'' t t'' k k'' e e'' ht
  obtain ⟨t', ht'⟩ := hh.exists_top t
  have k' : 0 < D'.R.k := by have := D'.R.m_add_three_le_k; omega
  have e' : (D'.eTau (D'.eTau.symm ⟨D'.R.tau1 t', (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩) : D'.R.GG) =
      D'.R.tau1 t' := by rw [Equiv.apply_symm_apply]
  obtain ⟨a, b⟩ := h _ _ t t' k k' e e' ht'
  obtain ⟨c, d⟩ := h' _ _ t' t'' k' k'' e' e'' (ht'.symm.trans ht)
  exact ⟨a.trans c, b.trans d⟩

theorem sameWord_self_iff (D : D7) (u u' : D.what₂.Word) : SameWord D u D u' ↔ D.hcW u = D.hcW u' := by
  constructor
  · intro h
    funext τ
    exact eq_of_heq (h.hc_eq τ τ HEq.rfl)
  · intro h
    exact ⟨SameHost.refl D, rfl, fun τ τ' e => by rw [D.eTau.injective (eq_of_heq e), h]⟩

theorem over_mono_eps {F : Pts} {Tr : ℝ → D7 → Prop} {ε ε' : ℝ} (h : F.RKRoomOver Tr ε) (hε : ε ≤ ε') : F.RKRoomOver Tr ε' := by
  obtain ⟨CR, CT, h⟩ := h
  refine ⟨|CR|, |CT|, h.mono 1 fun x hx i u ⟨D', u', h1, h2, ⟨h3, h4⟩, h5⟩ => ⟨D', u', h1, h2, ⟨?_, ?_⟩, h5⟩⟩
  all_goals
    have a1 : x ^ ε ≤ x ^ ε' := Real.rpow_le_rpow_of_exponent_le hx hε
    have a2 : 0 ≤ x ^ ε := by positivity
  · have : CR * x ^ ε ≤ |CR| * x ^ ε' := mul_le_mul (le_abs_self _) a1 a2 (abs_nonneg _)
    linarith
  · refine h4.trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) a1 a2 (by positivity))

theorem over_threshold {F : Pts} {Tr : ℝ → D7 → Prop} {ε : ℝ} (h : F.RKRoomOver Tr ε) :
    ∃ CR CT : ℝ, F.SomeAt fun x D u => Real.log (D.mem u).A.Xu ≤ (CR + CT * D.R.m) * x ^ ε := by
  obtain ⟨CR, CT, h⟩ := h
  exact ⟨CR, CT, h.mono 0 fun x _ i u ⟨D', u', _, _, ⟨h3, h4⟩, _⟩ => by linarith⟩

theorem log_T_le (D : D7) (u : D.what₂.Word) : Real.log ((D.mem u).A.T : ℝ) ≤ Real.log (D.mem u).A.Xu + 1 := by
  have hT : (0 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hf := f_mul_k_pos D.R
  have h1 := Real.log_le_log hT (T_lt_cap D u).le
  rw [Real.log_mul (by positivity) (Xu_pos D u).ne'] at h1
  have h2 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((D.R.f : ℝ) * D.R.k))
  have h3 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.k := by
    have := D.R.m_add_three_le_k
    have a : 0 < D.R.f * D.R.k := Nat.mul_pos (Nat.mul_pos two_pos D.R.ord_pos) (by omega)
    exact_mod_cast a
  have h4 : 1 / ((D.R.f : ℝ) * D.R.k) ≤ 1 := (div_le_one hf).2 h3
  linarith

def famQ (q : ℝ → LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A, fun x t => recd (q x) t 0 0 1, Pts.ne_of_forall fun _ => ⟨0⟩,
    fun _ _ _ => recd_sameHost ..⟩

theorem exists_big : ∃ q : ℝ → LvP, ∀ x, Real.exp x < (q x).T := by
  choose f hf using exists_lvP
  exact ⟨fun x => f ⌈Real.exp x⌉₊, fun x => lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hf _)⟩

theorem ev_lt (a b : ℝ) {δ : ℝ} (hδ : δ < 1) : ∃ x₁ : ℝ, ∀ x, x₁ ≤ x → a * x ^ δ + b < x := by
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).eventually_ge_atTop (2 * a)).and
      ((Filter.eventually_gt_atTop (0 : ℝ)).and (Filter.eventually_gt_atTop (2 * b))))
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨h1, h0, h2⟩ := hx₁ x hx
  have e : x ^ (1 - δ) * x ^ δ = x := by rw [← Real.rpow_add h0]; simp
  have h7 := mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos h0 δ).le
  linarith

theorem lower_end (p : LvP) (q : ℝ → LvP) (hq : ∀ x, Real.exp x < (q x).T) {ε : ℝ} (hε : ε < 1 / 52) :
    ¬ (famQ q).RKWeakOver (cls p 0 1) ε := by
  rintro ⟨CT, h⟩
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x₁, hx₁⟩ := ev_lt 1 (1 + Real.log p.T) (by linarith : 13 * ε < 1)
  obtain ⟨i, u, D', u', ⟨t, rfl⟩, -, ⟨h3, -⟩, -⟩ := h (max x₀ x₁) (le_max_left _ _) ⟨(0 : Formalism.BasicNotions.Examples₂.R0.A)⟩
  have h1 := hx₁ _ (le_max_right x₀ x₁)
  have h4 := log_T_le ((famQ q).D (max x₀ x₁) i) u
  have h5 := hq (max x₀ x₁)
  have h6 : max x₀ x₁ < Real.log ((q (max x₀ x₁)).T : ℝ) := (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) h5)).2 h5
  have h7 : Real.log ((q (max x₀ x₁)).T : ℝ) ≤ Real.log (((famQ q).D (max x₀ x₁) i).mem u).A.Xu + 1 := h4
  have h8 : Real.log (((famQ q).D (max x₀ x₁) i).mem u).A.Xu - (max x₀ x₁) ^ (13 * ε) ≤ Real.log (p.T : ℝ) := h3
  linarith

theorem win_not_room (p : LvP) {ε : ℝ} (h0 : 0 < ε) (hε : ε < 1 / 52) :
    ∃ F : Pts, F.RKAll ∧ F.RKWin ∧ ¬ F.RKRoom ε ∧ ¬ F.RKRoomOver (cls p 0 1) ε := by
  obtain ⟨q, hq⟩ := exists_big
  refine ⟨famQ q, ⟨0, fun _ _ _ => ⟨(), (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩,
    ⟨0, fun x _ _ u₀ hu => ⟨(Formalism.BasicNotions.Examples₂.R0.ofNat u₀), Formalism.BasicNotions.Examples₂.R0.val_ofNat_of_lt hu, (recd_sameTops ..).2 rfl, (), (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩,
    ?_, fun h => lower_end p q hq hε (h.rkWeakOver h0)⟩
  rintro ⟨CR, CT, h⟩
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x₁, hx₁⟩ := ev_lt (CT * 2) 0 (by linarith : ε < 1)
  obtain ⟨i, u, ⟨-, h3⟩, -⟩ := h (max x₀ x₁) (le_max_left _ _) ⟨(0 : Formalism.BasicNotions.Examples₂.R0.A)⟩
  have h1 := hx₁ _ (le_max_right x₀ x₁)
  have h5 := hq (max x₀ x₁)
  have h6 : max x₀ x₁ < Real.log ((q (max x₀ x₁)).T : ℝ) := (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) h5)).2 h5
  have h4 : Real.log ((q (max x₀ x₁)).T : ℝ) ≤ CT * (2 : ℕ) * (max x₀ x₁) ^ ε := h3
  push_cast at h4
  linarith

theorem one_translate (p p' : LvP) (ε : ℝ) :
    ¬ (fam p (fun _ => 0) 1).RKWeakOver (fun _ D => D = recd p' 0 0 0 1) ε := by
  rintro ⟨CT, x₀, h⟩
  have key : ∀ u₀ : ℕ, u₀ < Formalism.BasicNotions.Examples₂.R0.n → (0 : Formalism.BasicNotions.Examples₂.R0.A).val = u₀ := by
    intro u₀ hu
    obtain ⟨i, hi, -, u, D', u', rfl, h2, -⟩ := h x₀ le_rfl (0 : Formalism.BasicNotions.Examples₂.R0.A) u₀ hu
    have e : i = (0 : Formalism.BasicNotions.Examples₂.R0.A) := ((recd_sameWord p i 0 0 1 u p' 0 0 0 1 u').1 h2).1
    subst e
    exact hi
  exact zero_ne_one ((key 0 (by decide)).symm.trans (key 1 (by decide)))

def famTwo (p : LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A × Fin 2, fun _ i => recd p i.1 i.2 0 0, Pts.ne_of_forall fun _ => ⟨(0, 0)⟩,
    fun _ _ _ => recd_sameHost ..⟩

theorem two_weights (p p' : LvP) {ε : ℝ} (hε : 0 ≤ ε) :
    ¬ (famTwo p).RKRoomOver (cls p' 0 1) ε ∧ (famTwo p).RKRoomOver (fun x D => cls p' 0 1 x D ∨ cls p' 1 1 x D) ε := by
  constructor
  · rintro ⟨CR, CT, x₀, h⟩
    obtain ⟨i, -, hs, u, D', u', ⟨t, rfl⟩, h2, -⟩ := h x₀ le_rfl ((0 : Formalism.BasicNotions.Examples₂.R0.A), (1 : Fin 2)) 0
      (show 0 < Formalism.BasicNotions.Examples₂.R0.n by decide)
    have a := (recd_sameTops p i.1 i.2 0 0 p 0 (1 : Fin 2) 0 0).1 hs
    have b := ((recd_sameWord p i.1 i.2 0 0 u p' t 0 0 1 u').1 h2).2
    rw [b] at a
    exact absurd a (by decide)
  · obtain ⟨C, h⟩ := exists_const (Real.log (xOf p)) (Real.log p'.T) hε
    refine ⟨C, C, 1, fun x hx i₀ u₀ hu => ⟨((Formalism.BasicNotions.Examples₂.R0.ofNat u₀), i₀.2), Formalism.BasicNotions.Examples₂.R0.val_ofNat_of_lt hu, (recd_sameTops ..).2 rfl, (),
      recd p' (Formalism.BasicNotions.Examples₂.R0.ofNat u₀) i₀.2 0 1, (), ?_, (recd_sameWord ..).2 ⟨rfl, rfl⟩, h x hx, (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩
    obtain ⟨t, c⟩ := i₀
    fin_cases c
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

def clsN (p : LvP) (N : ℝ → ℕ) : ℝ → D7 → Prop := fun x D => ∃ t, D = recd p t 0 (N x) 1

theorem half_over (p p' : LvP) {ε : ℝ} (hε : 0 < ε) :
    (fam p (fun _ => 0) 0).RKWeakOver (clsN p' fun _ => 1) ε ∧ ¬ (fam p (fun _ => 0) 0).RKRoomOver (clsN p' fun _ => 1) ε := by
  constructor
  · obtain ⟨C, h⟩ := exists_const (Real.log (xOf p)) (Real.log p'.T) hε.le
    obtain ⟨x₁, hx₁⟩ := room_le_and_share_le hε C
    refine ⟨C, fam_someAt p _ _ (max 1 x₁) fun x hx t => ?_⟩
    obtain ⟨h1, h2⟩ := hx₁ x (le_of_max_le_right hx)
    obtain ⟨h3, h4⟩ := h x (le_of_max_le_left hx)
    refine ⟨recd p' t 0 1 1, (), ⟨t, rfl⟩, (recd_sameWord ..).2 ⟨rfl, rfl⟩, ⟨le_trans (sub_le_sub_left h1 _) h3, h4⟩,
      (recd_share p' t 0 1 () _).2 ?_⟩
    push_cast
    linarith
  · refine Pts.not_rkRoomOver ?_
    rintro x D u ⟨t, rfl⟩ h
    exact absurd ((rankCondition_rankOne_iff_eq_zero p' t 0 1 u).1 h) one_ne_zero

theorem thin_over (p p' : LvP) {ε : ℝ} (h52 : ε < 1 / 52) :
    ¬ (fam p (fun _ => 0) 1).RKWeakOver (clsN p' fun x => ⌈x⌉₊) ε := by
  rintro ⟨CT, h⟩
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨i, u, D', u', ⟨t, rfl⟩, -, -, hu⟩ := h (max x₀ 1) (le_max_left _ _) ⟨(0 : Formalism.BasicNotions.Examples₂.R0.A)⟩
  have hu' := (recd_share p' t 0 ⌈max x₀ 1⌉₊ u' _).1 hu
  have hx : 1 ≤ max x₀ 1 := le_max_right _ _
  clear hu u' u i h
  generalize max x₀ 1 = x at hx hu'
  have h1 : x ^ (-1 : ℝ) ≤ x ^ (-(12 * ε)) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 := Nat.le_ceil x
  have h3 : x⁻¹ * x = 1 := inv_mul_cancel₀ (by linarith)
  have h4 : 0 < x⁻¹ := by positivity
  have h5 : x⁻¹ * ((⌈x⌉₊ : ℝ) + 1) ≤ x ^ (-(12 * ε)) * ((⌈x⌉₊ : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
  nlinarith

theorem free_class (p : LvP) {ε : ℝ} (hε : 0 ≤ ε) : (fam p (fun _ => 0) 0).RKRoomOver (fun _ _ => True) ε :=
  (fam_over p p 0 hε).mono fun _ _ _ => trivial

def famSome (p : LvP) : Pts :=
  ⟨fun _ => Formalism.BasicNotions.Examples₂.R0.A × Fin 2, fun _ i => recd p i.1 0 i.2 1, Pts.ne_of_forall fun _ => ⟨(0, 0)⟩,
    fun _ _ _ => recd_sameHost ..⟩

theorem win_not_all (p : LvP) : (famSome p).RKWin ∧ ¬ (famSome p).RKAll := by
  constructor
  · exact ⟨0, fun x _ _ u₀ hu => ⟨((Formalism.BasicNotions.Examples₂.R0.ofNat u₀), (0 : Fin 2)), Formalism.BasicNotions.Examples₂.R0.val_ofNat_of_lt hu, (recd_sameTops ..).2 rfl, (),
      (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩
  · rintro ⟨x₀, h⟩
    obtain ⟨u, hu⟩ := h x₀ le_rfl ((0 : Formalism.BasicNotions.Examples₂.R0.A), (1 : Fin 2))
    exact absurd ((rankCondition_rankOne_iff_eq_zero p 0 0 (1 : Fin 2) u).1 hu) (by decide)

theorem hyp_over (p p' : LvP) :
    HypAll (fun _ => Pts) (fun _ F => F = fam p (fun _ => 0) 0) (fun _ F => F) (fun ε F => F.RKRoomOver (cls p' 0 1) ε) ∧
    ¬ HypEx (fun _ => Pts) (fun _ F => F = fam p (fun _ => 0) 1) (fun _ F => F) (fun ε F => F.RKRoomOver (cls p' 0 0) ε) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ε h0 - F rfl
    exact fam_over p p' 0 h0.le
  · obtain ⟨ε, -, -, -, F, rfl, hF⟩ := h 1 one_pos
    exact (fam_not_over p p' 1 ε).1 hF

end GlobalTheory.Core.RkOverModel

end
