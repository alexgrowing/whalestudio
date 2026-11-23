import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq
import Formalism.SharpRestriction.FamCore
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowGat
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfEqMulIntegral

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ NumberField Module

theorem sameTops_iff₂ {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hk : D.R.k = D'.R.k) :
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

def Pts.ofFam {ε : ℝ} (F : FamCore ε) : Pts where
  Ix := F.Ix
  D := F.D
  Ix_ne y := let ⟨x, h, _, _, hn⟩ := F.exists_pt y; ⟨x, h, hn⟩
  same x i i' := ⟨F.R_eq x i i', (F.TT_eq x i).trans (F.TT_eq x i').symm, F.realisedChain_torus_eq x i i', F.q_eq x i i', F.d_eq x i i',
    F.g_eq x i i', (F.pde_eq x i i').1, (F.pde_eq x i i').2, F.QS_eq x i i', fun p h h' => by
      have e := congrFun (F.art_eq x i i') p
      unfold artNum at e
      rw [dif_pos h, dif_pos h'] at e
      exact Prod.mk.inj e⟩

theorem Pts.ofFam_covered {ε : ℝ} (F : FamCore ε) : (Pts.ofFam F).Covered := by
  refine ⟨F.x1 + 1, fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2⟩ := F.coverS x (by linarith) i₀ u₀ hu
  exact ⟨i, h1, (sameTops_iff₂ (F.L x i) (F.L x i₀) (congrArg Ranks.k (F.R_eq x i i₀))).2 h2⟩

theorem Pts.ofFam_rkWin {ε : ℝ} (F : FamCore ε) (h : (Pts.ofFam F).RKAll) : (Pts.ofFam F).RKWin :=
  h.rkWin (Pts.ofFam_covered F)

namespace FamInh

structure LvP where
  T : ℕ
  prime : T.Prime
  big : 991 < T
  π : 𝓞 H0.E
  mem : (π : H0.E) ∈ H0.K
  norm : (π : H0.E) * H0.conj (π : H0.E) = (T : H0.E)
  cong : (π - 1) ∈ Ideal.span {((H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2 : ℕ) : 𝓞 H0.E)}

instance (p : LvP) : Fact p.T.Prime := ⟨p.prime⟩

theorem exists_lvP (N : ℕ) : ∃ p : LvP, N < p.T := by
  obtain ⟨π, p, hp, hN, hK, hn, hc, -⟩ := GlobalTheory.Mem.NormPrime.exists_norm_prime R0 H0 (H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2) 1 (max N 991)
    (by rw [modulus0]; norm_num) (Nat.coprime_one_left _)
  exact ⟨⟨p, hp, lt_of_le_of_lt (le_max_right _ _) hN, π, hK, hn, by simpa using hc⟩, lt_of_le_of_lt (le_max_left _ _) hN⟩

abbrev Ht (p : LvP) (t : R0.A) : Host R0 :=
  { H0 with
    TT := Finset.univ
    u0 := t
    levelPrimes := insert p.T H0.levelPrimes
    g_level := fun i => Finset.mem_insert_of_mem (H0.g_level i)
    pde_level := ⟨Finset.mem_insert_of_mem H0.pde_level.1, Finset.mem_insert_of_mem H0.pde_level.2⟩
    level_coprimeS := fun l hl => (Finset.mem_insert.1 hl).elim
      (fun e => by
        rw [e]
        exact Nat.Coprime.pow_right (2 + 2) ((Nat.coprime_primes p.prime Nat.prime_two).2 (by have := p.big; omega)))
      (H0.level_coprimeS l)
    ccK_coprime := fun q _ => by
      rw [show H0.ccK = ⊤ from rfl, Ideal.absNorm_top]; exact Nat.coprime_one_left q }

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

theorem tH (p : LvP) (t : R0.A) : THyp (Ht p t) := ⟨exampleHost_typeHypothesis.cond, exampleHost_typeHypothesis.bb, exampleHost_typeHypothesis.jac⟩

def gap (p : LvP) (t : R0.A) : LocalGap (Ht p t) := LocalGap.localGapOfRecord GlobalTheory.Mem.nonempty_record_of_locStage.some _

def lbl (p : LvP) (t : R0.A) : Lbl (Ht p t) :=
  (lbl_nonempty (Ht p t) (tH p t) 5 (by norm_num) (by decide) (by decide)).some

theorem LvP.ne_two (p : LvP) : p.T ≠ 2 := by have := p.big; omega

theorem LvP.ne_pde (p : LvP) : p.T ≠ H0.pde ∧ p.T ≠ H0.pde' := by
  have := p.big
  exact ⟨show p.T ≠ 751 by omega, show p.T ≠ 991 by omega⟩

set_option maxHeartbeats 1600000 in

def recd (p : LvP) (t : R0.A) (c N : ℕ) (s : ℂ) : D7 :=
  letI := (Ht p t).cmStar
  hostLevelRecord (Ht p t) (W := Unit) () (fun _ _ => hcA c) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      simp only [hcA, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => pkg N) (fun _ => p.T) (dstarOf p.T) (dstarOf_pos p.T) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 p.T) exampleHost_type_primes_split (tH p t) (fun _ => Finset.mem_insert_self _ _) (fun _ => p.ne_pde) (fun _ => p.π)
    (fun _ => p.mem) (fun _ => p.norm) (fun _ => p.cong)
    (fun _ i _ => ((hostSpacesOfNorm (Ht p t) p.T (p.π : (Ht p t).E) p.norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm (Ht p t) p.T (p.π : (Ht p t).E) p.norm).X i).standardTuple_isLattice)
    (gap p t) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl p t) (fun _ => p.ne_two) (fun _ _ => perS N s) (fun _ => ⊤)
    (localDataAtServedPlace' (Ht p t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => p.T) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes (Ht p t) (fun _ _ => hcA c) (fun _ : Unit => pkg N) (fun _ => p.T) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

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

variable (p : LvP)

theorem recd_dU (t c N s u) : dU (recd p t c N s) u = N + 1 :=
  (atTN_du (fun _ : Tau2 R0 => hcA c) (pkg N) p.T (dstarOf p.T) (dstarOf_pos p.T) 1 one_pos 2 one_lt_two p.ne_two).trans (by simp)

theorem columnRank_eq_one_of_rankOne (t c N u) : rkC ((recd p t c N 1).mem u).C ((recd p t c N 1).mem u).A ((recd p t c N 1).mem u).P = 1 :=
  rk_one (fun _ : Tau2 R0 => hcA c) N p.T (dstarOf p.T) (dstarOf_pos p.T) p.ne_two

theorem columnRank_eq_zero_of_rankZero (t c N u) : rkC ((recd p t c N 0).mem u).C ((recd p t c N 0).mem u).A ((recd p t c N 0).mem u).P = 0 :=
  rk_zero (fun _ : Tau2 R0 => hcA c) N p.T (dstarOf p.T) (dstarOf_pos p.T)

theorem rankCondition_rankOne_iff_eq_zero (t c N u) : RK (recd p t c N 1) u ↔ N = 0 := by
  show dU _ u < 2 * _ ↔ _
  rw [recd_dU, columnRank_eq_one_of_rankOne]; omega

theorem not_rankCondition_rankZero (t c N u) : ¬ RK (recd p t c N 0) u := by
  show ¬ dU _ u < 2 * _
  rw [recd_dU, columnRank_eq_zero_of_rankZero]; omega

theorem recd_share (t c N u) (ρ : ℝ) : RKShare ρ (recd p t c N 1) u ↔ ρ * ((N : ℝ) + 1) ≤ 1 := by
  unfold RKShare
  rw [recd_dU, columnRank_eq_one_of_rankOne]
  simp

theorem recd_sameHost (t c N s p' t' c' N' s') : SameHost (recd p t c N s) (recd p' t' c' N' s') :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem recd_sameTops (t c N s p' t' c' N' s') : SameTops (recd p t c N s) (recd p' t' c' N' s') ↔ c = c' := by
  constructor
  · intro H
    have := (H ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩ ⟨R0.tau1 0, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩
      ⟨(0 : R0.A), Finset.mem_univ _⟩ ⟨(0 : R0.A), Finset.mem_univ _⟩
      (show 0 < R0.k by decide) (show 0 < R0.k by decide) rfl rfl rfl).1
    have h2 : hc0.u ⟨0, by decide⟩ + (c : ℚ) = hc0.u ⟨0, by decide⟩ + (c' : ℚ) := this
    exact_mod_cast add_left_cancel h2
  · rintro rfl τ τ' _ _ h h' _ _ _
    exact ⟨rfl, rfl⟩

theorem recd_sameWord (t c N s u p' t' c' N' s' u') :
    SameWord (recd p t c N s) u (recd p' t' c' N' s') u' ↔ t = t' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨Formalism.HC.Frame.A.val_injective _ h.unitVector_val_eq, (recd_sameTops ..).1 h.sameTops⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨recd_sameHost .., rfl, fun _ _ _ => HEq.rfl⟩

theorem val_cast (u₀ : ℕ) (h : u₀ < R0.n) : (R0.ofNat u₀ : R0.A).val = u₀ := R0.toFrame.val_ofNat_of_lt h

theorem exists_const (a b : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → a - C * x ^ ε ≤ b ∧ b ≤ C * (2 : ℕ) * x ^ ε := by
  refine ⟨|a| + |b|, fun x hx => ?_⟩
  have h2 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε
  have h3 := le_abs_self a
  have h4 := le_abs_self b
  have h5 := neg_abs_le b
  have h6 := abs_nonneg a
  have h7 := abs_nonneg b
  have h8 : |a| + |b| ≤ (|a| + |b|) * x ^ ε := le_mul_of_one_le_right (by linarith) h2
  refine ⟨by linarith, ?_⟩
  push_cast
  nlinarith

def fam (N : ℝ → ℕ) (s : ℂ) : Pts :=
  ⟨fun _ => R0.A, fun x t => recd p t 0 (N x) s, Pts.ne_of_forall fun _ => ⟨0⟩, fun _ _ _ => recd_sameHost ..⟩

def xOf : ℝ := ((recd p 0 0 0 0).mem ()).A.Xu

theorem fam_someAt (N : ℝ → ℕ) (s : ℂ) {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (x₀ : ℝ)
    (h : ∀ x, x₀ ≤ x → ∀ t, Q x (recd p t 0 (N x) s) ()) : (fam p N s).SomeAt Q :=
  ⟨x₀, fun x hx _ u₀ hu => ⟨R0.ofNat u₀, val_cast u₀ hu, (recd_sameTops ..).2 rfl, (), h x hx _⟩⟩

theorem fam_yes {ε : ℝ} (hε : 0 < ε) : (fam p (fun _ => 0) 1).RKAll ∧ (fam p (fun _ => 0) 1).RKWin ∧
    (fam p (fun _ => 0) 1).RKRoom ε ∧ (fam p (fun _ => 0) 1).RKWeak ε := by
  have h : (fam p (fun _ => 0) 1).RKRoom ε := by
    obtain ⟨C, h⟩ := exists_const (Real.log (xOf p)) (Real.log p.T) hε.le
    exact ⟨C, C, fam_someAt p _ _ 1 fun x hx t => ⟨h x hx, (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩
  exact ⟨⟨0, fun _ _ _ => ⟨(), (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩, h.rkWin, h, h.rkWeak hε⟩

theorem fam_zero (N : ℝ → ℕ) (ε : ℝ) :
    ¬ (fam p N 0).RKAll ∧ ¬ (fam p N 0).RKWin ∧ ¬ (fam p N 0).RKRoom ε ∧ ¬ (fam p N 0).RKWeak ε := by
  have hw : ¬ (fam p N 0).RKWin := fun h => by
    obtain ⟨x₀, h⟩ := Pts.SomeAt.exists h
    obtain ⟨i, u, hu⟩ := h x₀ le_rfl ⟨(0 : R0.A)⟩
    exact not_rankCondition_rankZero _ _ _ _ _ hu
  refine ⟨?_, hw, fun h => hw h.rkWin, ?_⟩
  · rintro ⟨x₀, h⟩
    obtain ⟨u, hu⟩ := h x₀ le_rfl (0 : R0.A)
    exact not_rankCondition_rankZero _ _ _ _ _ hu
  · rintro ⟨CT, h⟩
    obtain ⟨x₀, h⟩ := h.exists
    obtain ⟨i, u, -, hu, -⟩ := h x₀ le_rfl ⟨(0 : R0.A)⟩
    exact absurd (columnRank_eq_zero_of_rankZero p i 0 _ u) hu.ne'

theorem fam_half {ε : ℝ} (hε : 0 < ε) : (fam p (fun _ => 1) 1).RKWeak ε ∧ ¬ (fam p (fun _ => 1) 1).RKWin := by
  constructor
  · obtain ⟨C, h⟩ := exists_const (Real.log (xOf p)) (Real.log p.T) hε.le
    obtain ⟨x₁, hx₁⟩ := room_le_and_share_le hε C
    refine ⟨C, fam_someAt p _ _ (max 1 x₁) fun x hx t => ?_⟩
    obtain ⟨h1, h2⟩ := hx₁ x (le_of_max_le_right hx)
    obtain ⟨h3, h4⟩ := h x (le_of_max_le_left hx)
    refine ⟨⟨le_trans (sub_le_sub_left h1 _) h3, h4⟩, (recd_share p t 0 1 () _).2 ?_⟩
    push_cast
    linarith
  · intro h
    obtain ⟨x₀, h⟩ := Pts.SomeAt.exists h
    obtain ⟨i, u, hu⟩ := h x₀ le_rfl ⟨(0 : R0.A)⟩
    exact absurd ((rankCondition_rankOne_iff_eq_zero p i 0 1 u).1 hu) one_ne_zero

def cls (c : ℕ) (s : ℂ) : ℝ → D7 → Prop := fun _ D => ∃ t, D = recd p t c 0 s

theorem fam_over (p' : LvP) (s : ℂ) {ε : ℝ} (hε : 0 ≤ ε) : (fam p (fun _ => 0) s).RKRoomOver (cls p' 0 1) ε := by
  obtain ⟨C, h⟩ := exists_const (Real.log (xOf p)) (Real.log p'.T) hε
  exact ⟨C, C, fam_someAt p _ _ 1 fun x hx t =>
    ⟨recd p' t 0 0 1, (), ⟨t, rfl⟩, (recd_sameWord ..).2 ⟨rfl, rfl⟩, h x hx, (rankCondition_rankOne_iff_eq_zero ..).2 rfl⟩⟩

theorem fam_not_over (p' : LvP) (s : ℂ) (ε : ℝ) :
    ¬ (fam p (fun _ => 0) s).RKRoomOver (cls p' 0 0) ε ∧ ¬ (fam p (fun _ => 0) s).RKRoomOver (cls p' 1 1) ε := by
  constructor
  · refine Pts.not_rkRoomOver ?_
    rintro x D u ⟨t, rfl⟩
    exact not_rankCondition_rankZero _ _ _ _ _
  · rintro ⟨CR, CT, h⟩
    obtain ⟨x₀, h⟩ := h.exists
    obtain ⟨i, u, D', u', ⟨t, rfl⟩, h2, -⟩ := h x₀ le_rfl ⟨(0 : R0.A)⟩
    exact absurd ((recd_sameWord p i 0 0 s u p' t 1 0 1 u').1 h2).2 zero_ne_one

theorem room_used {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ (F : Pts) (Tr : ℝ → D7 → Prop), F.RKRoomOver Tr ε ∧ ¬ F.RKWin ∧ ∀ x i u D' u', Tr x D' →
      (1 + 1 / (((F.D x i).R.f : ℝ) * (F.D x i).R.k)) * ((F.D x i).mem u).A.Xu < ((D'.mem u').A.T : ℝ)) ∧
    (∃ (F : Pts) (Tr : ℝ → D7 → Prop), F.RKRoomOver Tr ε ∧ ¬ F.RKWin ∧ ∀ x i u D' u', Tr x D' →
      ((D'.mem u').A.T : ℝ) < ((F.D x i).mem u).A.Tstar) := by
  obtain ⟨p, -⟩ := exists_lvP 0
  obtain ⟨p', hp⟩ := exists_lvP (max p.T ⌈(1 + 1 / ((R0.f : ℝ) * R0.k)) * xOf p⌉₊)
  refine ⟨⟨fam p (fun _ => 0) 0, cls p' 0 1, fam_over p p' 0 hε, (fam_zero p _ ε).2.1, ?_⟩,
    ⟨fam p' (fun _ => 0) 0, cls p 0 1, fam_over p' p 0 hε, (fam_zero p' _ ε).2.1, ?_⟩⟩
  · rintro x i u D' u' ⟨t, rfl⟩
    exact lt_of_le_of_lt (Nat.le_ceil ((1 + 1 / ((R0.f : ℝ) * R0.k)) * xOf p))
      (show _ < (p'.T : ℝ) by exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hp)
  · rintro x i u D' u' ⟨t, rfl⟩
    exact lt_of_lt_of_eq (show (p.T : ℝ) < p'.T by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hp)
      (atTToy_Tstar_eq Tau0 p'.T).symm

theorem not_over_of_large {ε : ℝ} (hε : ε < 1) (q : ℝ → LvP) (hq : ∀ x, Real.exp x < (q x).T) :
    ¬ (fam p (fun _ => 0) 1).RKRoomOver (fun x => cls (q x) 0 1 x) ε := by
  rintro ⟨CR, CT, h⟩
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by linarith : 0 < 1 - ε)).eventually_ge_atTop (CT * 2)).and (Filter.eventually_gt_atTop (0 : ℝ)))
  obtain ⟨i, u, D', u', ⟨t, rfl⟩, -, ⟨-, h3⟩, -⟩ := h (max x₀ x₁) (le_max_left _ _) ⟨(0 : R0.A)⟩
  obtain ⟨h1, h0⟩ := hx₁ (max x₀ x₁) (le_max_right _ _)
  have h4 : Real.log ((q (max x₀ x₁)).T : ℝ) ≤ CT * (2 : ℕ) * (max x₀ x₁) ^ ε := h3
  have h5 := hq (max x₀ x₁)
  generalize max x₀ x₁ = x at h1 h0 h4 h5
  have h6 : x < Real.log ((q x).T : ℝ) := (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos x) h5)).2 h5
  have e : x ^ (1 - ε) * x ^ ε = x := by rw [← Real.rpow_add h0]; simp
  have h7 := mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos h0 ε).le
  push_cast at h4
  linarith

example : HypEx (fun _ => Pts) (fun _ F => F = fam p (fun _ => 0) 1 ∨ F = fam p (fun _ => 0) 0) (fun _ F => F)
      (fun ε F => F.RKRoom ε) ∧
    ¬ HypAll (fun _ => Pts) (fun _ F => F = fam p (fun _ => 0) 1 ∨ F = fam p (fun _ => 0) 0) (fun _ F => F)
      (fun ε F => F.RKRoom ε) := by
  refine ⟨fun δ hδ => ?_, fun h => (fam_zero p _ _).2.2.1 (h (1 / 100) (by norm_num) (by norm_num) _ (Or.inr rfl))⟩
  have h0 : 0 < min (δ / 2) (1 / 100) := by positivity
  exact ⟨_, h0, (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by norm_num), _, Or.inl rfl,
    (fam_yes p h0).2.2.1⟩

end FamInh

end GlobalTheory.Core.Rk

end
