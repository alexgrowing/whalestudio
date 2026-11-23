import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ShortVectorBoundLeKappa
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofUMapSqSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmMem

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem l2_nonneg_GT {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.setAverage_eq]
  refine smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (MeasureTheory.integral_nonneg fun v => ?_)
  unfold GT.ptN2
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem zeroMode [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ∃ β ∈ (Col.YB hI hP 1).Sec 1,
      (∀ w : Vsp X.dim, ∀ T M : ℝ, (∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
          ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T) →
        (∀ t, (Col.YB hI hP 1).ptN2 1 β t ≤ M) →
        Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T) ∧
      ∃ a : Fin (Module.finrank ℝ (IR I)) → IR I, (∀ i, (a i : Vsp X.dim) ∈ I) ∧
        (Col.ob (IR I)).toBasis.det a ≠ 0 ∧
        |(Col.ob (IR I)).toBasis.det a| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
          (Col.YB hI hP 1).l2 1 β ≤ X.l2 1 s :=
  ⟨ZM.zmB hI s, zm_mem hI hP hs, fun w T M hT hM => zm_pt hI hP hs w T M hT hM, ZM.Ib hI,
    ZM.Ib_mem hI, ZM.Ib_det_ne hI, zm_norm hI hP hs⟩

theorem tof_yb_sup [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (hS : GSupStatement) {β : EuclideanSpace ℂ
    (Fin (Col.gB (IR I))) → ℂ} (hβ : β ∈ (Col.YB hI hP 1).Sec 1) (t : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) :
    (Col.YB hI hP 1).ptN2 1 β t ≤ Real.exp P.p1 ^ 2 * (Col.YB hI hP 1).l2 1 β := by
  set Y := Col.YB hI hP 1 with hY
  have key := hS (Fin (Col.gB (IR I))) Y 1 le_rfl β hβ t
  rw [Fintype.card_fin] at key
  set g : ℕ := X.gA with hg
  have hgbg : (Col.gB (IR I)) ≤ g := by
    have h1 := Submodule.finrank_le (Col.V2 (IR I))
    rw [finrank_euclideanSpace, X.card_idx] at h1
    exact h1
  have hg2 : 2 ≤ g := P.hfr
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqth := one_le_sqrt_q_th P
  have hth := Col.th_pos P
  set y : ℝ := 1 + 6 * Real.sqrt (g * P.q) with hy
  have hy1 : 1 ≤ y := by have := Real.sqrt_nonneg (g * P.q); linarith
  have hl0 := l2_nonneg_GT Y 1 β
  have hbase : 1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤ y := by
    rcases Nat.eq_zero_or_pos (Col.gB (IR I)) with h0 | hpos
    · have h00 : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) = 0 := by rw [h0]; simp
      rw [h00]; simp; linarith
    · have hla : P.th ≤ Y.la1 := by
        apply le_csInf
        · refine ⟨‖Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩‖, Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩, Submodule.subset_span ⟨_, rfl⟩,
            Y.b.ne_zero _, rfl⟩
        · rintro _ ⟨x, hx, hne, rfl⟩
          exact Col.GB_norm hI ((Col.YB_lat hI hP 1).1 hx) hne
      have hla0 : 0 < Y.la1 := lt_of_lt_of_le hth hla
      have hpi : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) := by
        rw [Nat.cast_one, one_mul, Real.one_le_sqrt]; linarith [Real.pi_gt_three]
      have hden : 0 < Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1 := by positivity
      have hA : 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤
          6 * Real.sqrt (g * P.q) := by
        rw [div_le_iff₀ hden]
        have hgb' : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) ≤ Real.sqrt (2 * g) := by
          apply Real.sqrt_le_sqrt; have : ((Col.gB (IR I)) : ℝ) ≤ g := by exact_mod_cast hgbg
          linarith
        rw [Real.sqrt_mul (by norm_num) (g : ℝ), Real.sqrt_mul hgpos.le] at *
        have hs2 : Real.sqrt 2 ≤ 1.5 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hsg := Real.sqrt_pos.2 hgpos
        have hsq := Real.sqrt_nonneg (P.q : ℝ)
        have h1 : 1 ≤ Real.sqrt P.q * Y.la1 :=
          le_trans hqth (mul_le_mul_of_nonneg_left hla hsq)
        have h2 : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * (Real.sqrt P.q * Y.la1) := by
          nlinarith
        nlinarith
      rw [hy]; linarith
  have hB : 2 * ((1 : ℕ) : ℝ) ^ (Col.gB (IR I)) * (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
      (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ Real.exp P.p1 ^ 2 := by
    have hp : Real.exp P.p1 ^ 2 = Real.exp 2 * y ^ (2 * g) := by
      rw [← Real.exp_nat_mul, Par.p1, ← hg, ← hy]
      rw [show ((2 : ℕ) : ℝ) * (1 + g * Real.log y) = 2 + ((2 * g : ℕ) : ℝ) * Real.log y by
        push_cast; ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [hp]
    have h2e : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h0 : 0 ≤ 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) := by
      apply div_nonneg (by positivity)
      apply mul_nonneg (Real.sqrt_nonneg _)
      rw [GT.la1]; apply Real.sInf_nonneg; rintro _ ⟨x, -, -, rfl⟩; exact norm_nonneg _
    have hb : (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
        (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ y ^ (2 * g) := by
      calc _ ≤ y ^ (2 * (Col.gB (IR I))) := pow_le_pow_left₀ (by linarith) hbase _
        _ ≤ y ^ (2 * g) := pow_le_pow_right₀ hy1 (by omega)
    exact mul_le_mul (by rw [Nat.cast_one, one_pow, mul_one]; exact h2e) hb
      (pow_nonneg (by linarith) _) (by positivity)
  exact le_trans key (mul_le_mul_of_nonneg_right hB hl0)

theorem perFactor_of [IsCMField E] (hx : Ext.All) (hS : GSupStatement) {X : PT E} {DF : ℕ}
    (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hph : 0 < P.ph) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    PerFactor P I s := by
  have hP : Ext.PackingCount := hx.1
  have hG : Ext.GHadamard := hx.2.2.2.1
  obtain ⟨β, hβ, hpt, a, haI, hdet, hl2⟩ := zeroMode hI hP hs
  set Y := Col.YB hI hP 1 with hY
  have hLS := tof_yb_sup hI hP hS hβ
  have hl0 := l2_nonneg_GT Y 1 β
  intro w
  obtain ⟨y0, hy0, hsum⟩ := tof_gauss_min_sum P hI hP (uMap I w) (isU_uMap I w).1
  refine ⟨y0, hy0, ?_⟩
  set d := dstar (E := E) P.m with hd
  set Eg := Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y0‖ ^ 2) with hEg
  set T := 2 * (3 * (d : ℝ)) ^ d * Eg with hT
  have hpw := hpt w T (Real.exp P.p1 ^ 2 * Y.l2 1 β) hsum hLS
  have hp2 : Real.exp P.p2 = 2 * (3 * (d : ℝ)) ^ d := by
    rw [Par.p2, Real.exp_log]
    have h := tof_two_le_dstar P
    have : (2 : ℝ) ≤ d := by exact_mod_cast h
    exact mul_pos two_pos (pow_pos (by linarith) _)
  have hRHS : 0 ≤ Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)) (Real.exp_pos _).le
  rcases hl0.lt_or_eq with hlpos | hleq
  · set c := |(Col.ob (IR I)).toBasis.det a| with hc
    have hcpos : 0 < c := abs_pos.2 hdet
    have h2pos : 0 < (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hcl : 0 < c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := mul_pos hcpos h2pos
    have hsl : 0 < X.l2 1 s := lt_of_lt_of_le (by positivity) hl2
    have hcov := tof_covol_lb P hI hG (Col.ob (IR I)) a haI hdet
    have hinv := tof_inv_sqrt_le P hph (Module.finrank ℝ (IR I)) (tof_finrank_IR_le P hI) c hcpos hcov
    have hden : Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β) ≤
        Real.sqrt (X.l2 1 s) := by
      rw [← Real.sqrt_mul hcl.le]; exact Real.sqrt_le_sqrt hl2
    have hnum : Real.sqrt (X.ptN2 1 s fun _ => w) ≤
        Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le] at hpw
      exact hpw
    have hsc := Real.sqrt_pos.2 hcl
    have hsb := Real.sqrt_pos.2 hlpos
    rw [div_le_iff₀ (Real.sqrt_pos.2 hsl)]
    calc Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := hnum
      _ = Real.exp P.p1 * T * (1 / Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2))) *
            (Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β)) := by
          field_simp
      _ ≤ Real.exp P.p1 * T * (Real.exp d * (P.ka0 * P.ph) ^ ((d : ℝ) / 4)) *
            Real.sqrt (X.l2 1 s) := by
          have hTn : 0 ≤ T := by
            rw [hT]
            have h := tof_two_le_dstar P
            have : (2 : ℝ) ≤ d := by exact_mod_cast h
            exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
              (Real.exp_pos _).le
          have hA : 0 ≤ Real.exp P.p1 * T := mul_nonneg (Real.exp_pos _).le hTn
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv hA) hden (by positivity)
            (mul_nonneg hA (mul_nonneg (Real.exp_pos _).le
              (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)))
      _ = Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg *
            Real.sqrt (X.l2 1 s) := by
          rw [hT, ← hp2, Real.exp_add, Real.exp_add]; ring
  · rw [← hleq, mul_zero, Real.sqrt_zero, zero_mul] at hpw
    have : Real.sqrt (X.ptN2 1 s fun _ => w) = 0 := le_antisymm hpw (Real.sqrt_nonneg _)
    rw [this, zero_div]; exact hRHS

end

end ReciprocityTheory.ChartRestriction.G.I2
