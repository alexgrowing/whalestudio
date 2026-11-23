import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem archimedeanBoundTotalConstant_nonneg_le_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → 0 ≤ GlobalTheory.EtaAn.p16 E r q m 5 1 ∧ GlobalTheory.EtaAn.p16 E r q m 5 1 ≤ 200000 * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * r * L) ^ 2 := by
  intro E _ _ _ r q m L hL hf hr hm hmr hq hρ lρ lF lR lq
  have key := GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size E r q m 1 L hL hf hr hm hmr hq hρ lρ lF lR lq (by simp; positivity)
  have hd : ((ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℕ) : ℝ) = 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * m := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.dstar; push_cast; ring
  have hfR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd2 : (2 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) := by rw [hd]; nlinarith
  have hRR : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) := by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ hρ
  have p3nn : 0 ≤ GlobalTheory.EtaAn.p3 E r q m := by
    unfold GlobalTheory.EtaAn.p3
    have hs := Real.sqrt_nonneg (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)
    apply mul_nonneg (Nat.cast_nonneg _)
    have a1 : 0 ≤ Real.log (1 + 6 * Real.sqrt (((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) * q)) :=
      Real.log_nonneg (by linarith)
    have a2 : 0 ≤ Real.log (2 * (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (3 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ)) ^ ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m :=
        one_le_pow₀ (by linarith)
      linarith
    have a3 : (0 : ℝ) ≤ ((ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_nonneg a3 a1
    linarith
  have hN : Real.log ((1 : ℕ) : ℝ) ≤ Real.log (((max 1 1 * 5 ^ (8 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2) : ℕ)) : ℝ) := by
    rw [Nat.cast_one, Real.log_one]; exact Real.log_natCast_nonneg _
  refine ⟨?_, le_trans ?_ key.2⟩
  · unfold GlobalTheory.EtaAn.p16
    have l5 : 0 ≤ Real.log ((5 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have l1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
    have hA : (1 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 := by
      push_cast; nlinarith
    have hB : (1 : ℝ) ≤ 4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2 := by nlinarith
    have a5 : 0 ≤ Real.log (((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2 *
        (4 * ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) ^ 2)) :=
      Real.log_nonneg (by nlinarith)
    have t1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (r : ℝ) ^ 2) l5
    have t2 := mul_nonneg (by linarith : (0 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ 4 * r * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) m : ℝ) / 2) a5
    have t3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4) p3nn
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    rw [l1, zero_add]
    exact add_nonneg (mul_nonneg h5 (add_nonneg p3nn t1)) t2
  · unfold GlobalTheory.EtaAn.p16
    have h5 : (0 : ℝ) ≤ 2 * ((5 : ℕ) : ℝ) ^ 4 := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl (add_le_add hN le_rfl)) h5) le_rfl

theorem size_inequality_real : ∀ (rd c t b f r DF g0 g1 : ℝ), 1 ≤ rd → rd ≤ c → c ^ 36 * t ^ 150 ≤ Real.sqrt b → 11 ≤ t → 1 ≤ f → f ≤ t → 1 ≤ r → r ≤ t → 1 ≤ DF → DF ≤ b ^ 2 → b ^ 8 ≤ g0 → b ^ 8 ≤ g1 → (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ g0 * g1 := by
  intro rd c t b f r DF g0 g1 hrd hc hC ht hf1 hft hr1 hrt hD1 hDb hg0 hg1
  have ht1 : 1 ≤ t := by linarith
  have hc1 : 1 ≤ c := hrd.trans hc
  have hct : 1 ≤ c ^ 36 * t ^ 150 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc1) (one_le_pow₀ ht1)
  have hs1 : 1 ≤ Real.sqrt b := hct.trans hC
  have hb0 : 0 ≤ b := by
    by_contra h
    push_neg at h
    rw [Real.sqrt_eq_zero'.2 h.le] at hs1
    linarith
  have hbs := Real.sq_sqrt hb0
  have hb1 : 1 ≤ b := by nlinarith
  have hsb : Real.sqrt b ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hcb : c ^ 36 * t ^ 150 ≤ b := hC.trans hsb
  have ht7 : t ^ 7 ≤ b := by
    have e1 : t ^ 7 ≤ t ^ 150 := pow_le_pow_right₀ ht1 (by norm_num)
    have e2 : t ^ 150 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)
    linarith
  have hR : (rd ^ 7) ^ 4 ≤ b := by
    have e1 : (rd ^ 7) ^ 4 ≤ c ^ 28 := by rw [← pow_mul]; exact pow_le_pow_left₀ (by linarith) hc 28
    have e2 : c ^ 28 ≤ c ^ 36 := pow_le_pow_right₀ hc1 (by norm_num)
    have e3 : c ^ 36 ≤ c ^ 36 * t ^ 150 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    linarith
  have ht2 : t ^ 2 ≤ t ^ 7 := pow_le_pow_right₀ ht1 (by norm_num)
  have htt : t ≤ t ^ 7 := le_self_pow₀ ht1 (by norm_num)
  have h180 : 180 ≤ b := by
    have : (11 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7
    norm_num at this
    linarith
  have hfr : f * r ≤ b := by nlinarith
  have hrb : r ≤ b := by linarith
  have hY : 90 * (f * r + DF) ≤ 180 * b ^ 2 := by nlinarith
  have hg : b ^ 16 ≤ g0 * g1 := by
    have := mul_le_mul hg0 hg1 (by positivity) (by linarith [one_le_pow₀ (M₀ := ℝ) hb1 (n := 8)])
    rw [← pow_add] at this
    exact this
  have e1 : (rd ^ 7) ^ 4 * (90 * (f * r + DF)) * DF * r ≤ b * (180 * b ^ 2) * b ^ 2 * b := by
    have h0 : 0 ≤ (rd ^ 7) ^ 4 := by positivity
    have := mul_le_mul hR hY (by positivity) (by linarith)
    have := mul_le_mul this hDb (by linarith) (by positivity)
    exact mul_le_mul this hrb (by linarith) (by positivity)
  have e2 : b * (180 * b ^ 2) * b ^ 2 * b = 180 * b ^ 6 := by ring
  have e3 : 180 * b ^ 6 ≤ b ^ 16 := by
    have : b ^ 16 = b ^ 10 * b ^ 6 := by ring
    have h10 : b ≤ b ^ 10 := le_self_pow₀ hb1 (by norm_num)
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem sqrt_lt_th_real (q : ℕ) (M f R0 RR b s : ℝ) (hq : 1 ≤ q) (hb : 0 < b) (hM : (q : ℝ) * b ≤ M)
    (hf : 1 ≤ f) (hR : 1 ≤ R0 ^ 2) (hRR : 1 ≤ RR) (hs : M * s < b) :
    Real.sqrt s < Real.sqrt (f * R0 ^ 2 * RR ^ 3 / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hRR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hRR
  have h1 : 1 ≤ f * R0 ^ 2 * RR ^ 3 := by
    have := mul_le_mul hf hR zero_le_one (by linarith)
    nlinarith
  have hpos : 0 < f * R0 ^ 2 * RR ^ 3 / q := by positivity
  rcases le_or_gt s 0 with h0 | h0
  · rw [Real.sqrt_eq_zero'.2 h0]; exact Real.sqrt_pos.2 hpos
  · apply Real.sqrt_lt_sqrt h0.le
    rw [lt_div_iff₀ hq0]
    have : (q : ℝ) * b * s ≤ M * s := mul_le_mul_of_nonneg_right hM h0.le
    nlinarith

theorem level_ge {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {x : ℝ} {hx : Fm.x1 < x} {ι : Fm.Ix x} (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hL : 1 ≤ (Fm.L x ι).sc.L) :
    (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    congr 1
    exact p.fw.laws.toLawsM.pins.2.1.1
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have he : 3 * (Fm.L x ι).sc.L / Real.log 3 < (expL (Fm.L x ι).sc.L : ℝ) + 1 := Nat.lt_floor_add_one _
  have he' : (Fm.L x ι).sc.L ≤ (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 := by
    rw [div_lt_iff₀ hlog3p] at he
    nlinarith
  have hb : (Fm.L x ι).sc.b ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := by
    unfold Formalism.BasicNotions.Scale.b
    calc Real.exp (Fm.L x ι).sc.L ≤ Real.exp ((expL (Fm.L x ι).sc.L : ℝ) * Real.log 3) := Real.exp_le_exp.2 he'
      _ = (3 : ℝ) ^ expL (Fm.L x ι).sc.L := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
      _ ≤ (15 : ℝ) ^ expL (Fm.L x ι).sc.L := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [hM]
  push_cast
  exact mul_le_mul_of_nonneg_left hb (by positivity)

set_option maxHeartbeats 1000000 in

theorem params_sqrt_bounds : Size → Covers fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  intro _
  refine (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 6) GlobalTheory.CovTop.WtShape.wtN).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨A, -, a, ha⟩, ⟨C2, -, b0, hb0⟩⟩ := hh
  refine ⟨200000, by norm_num, max a b0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hW : WtNum p i (Fm.parT x hx ι).PP := hb0 x hx ((le_max_right _ _).trans hle) ι p hp i
  have S := Fm.sizes x hx ι
  have P := Fm.params x hx ι
  have hm4 := Formalism.L2.Pj.host_m_pow_four_le_f S
  have hf2 := Formalism.L2.Pj.host_f_sq_le_rd P
  have hrd16 := Formalism.L2.Pj.host_rd_ge_sixteen P
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have ef := Formalism.L2.Pj.hostSize_f (Fm.D x ι)
  have erd := Formalism.L2.Pj.hostSize_rd (Fm.D x ι)
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hLL := hN.big.2.2.2
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have hmR : (2 : ℝ) ≤ (Fm.D x ι).R.m := by exact_mod_cast a1
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (by linarith)
  have hb0' : 0 < (Fm.L x ι).sc.b := Real.exp_pos _

  have hq : (1 : ℝ) ≤ (Fm.D x ι).host.q := by exact_mod_cast (Fm.D x ι).host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ (Fm.D x ι).host.d := by exact_mod_cast (Fm.D x ι).host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ (Fm.D x ι).R.n := by exact_mod_cast (Fm.D x ι).R.ord_pos
  have hqd : (1 : ℝ) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by nlinarith
  have hs : Real.sqrt (((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hrdb : (Fm.D x ι).host.rdE ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      hc.trans ((le_self_pow₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have hlogrd : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [erd]
    have := Real.log_le_log (by linarith) hrdb
    unfold Formalism.BasicNotions.Scale.b at this
    rw [Real.log_exp] at this
    linarith

  have hlfr := hN.logfr.1
  have hlf : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [ef]
    have hf0 : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
    have := Real.log_le_log hf0 (le_mul_of_one_le_right hf0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.r))
    linarith
  have hlr : Real.log ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.L := by
    have hr0 : (0 : ℝ) < (Fm.D x ι).R.r := by linarith
    have := Real.log_le_log hr0 (le_mul_of_one_le_left hr0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.f))
    linarith
  have hg0 : ∀ k, (0 : ℝ) < (Fm.D x ι).host.g k := fun k => by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
  have hq1 : 1 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ((Fm.D x ι).host.g_prime 0).ne_zero ((Fm.D x ι).host.g_prime 1).ne_zero)
  have hlq : Real.log (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ 70 * (Fm.L x ι).sc.L := by
    push_cast
    rw [Real.log_mul (hg0 0).ne' (hg0 1).ne']
    linarith [hN.logg 0, hN.logg 1]
  have hP := archimedeanBoundTotalConstant_nonneg_le_bound (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m
    (Fm.L x ι).sc.L (by linarith) (by rw [ef]; omega) (by omega) (by omega) a5.2.1 hq1 (by rw [erd]; exact h1)
    hlogrd hlf hlr hlq
  rw [ef] at hP
  refine ⟨?_, hP.1, ?_, fun DF hDF hDFb => ⟨?_, ?_⟩⟩
  · rw [hW.sig.2.1]; unfold Formalism.BasicNotions.Ranks.sigW; omega
  ·
    have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have := mul_le_mul hfR hrR (by norm_num) (by linarith)
      nlinarith
    have hZ : zBase (Fm.L x ι) ^ 2 ≤ (Fm.parT x hx ι).PP :=
      (pow_le_pow_right₀ hZ1 (by norm_num)).trans hN.ppLow
    have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
      rw [hW.dim]
      have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne')
      exact_mod_cast this
    have hT0 : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ
    have hrow := hW.what₂.2
    have hTP : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP ≤ (Fm.L x ι).sc.b := by
      revert hrow hD1 hT0 hPP0 hL10
      generalize (lenT p i (Fm.parT x hx ι).PP : ℝ) = T
      generalize (Fm.parT x hx ι).PP = PP
      generalize (dimFlag (dat p i) : ℝ) = Dd
      generalize (Fm.L x ι).sc.L = L
      generalize (Fm.L x ι).sc.b = b
      intro hrow hD1 hT0 hPP0 hL10
      have e0 : 0 ≤ PP * T := mul_nonneg hPP0 hT0
      have e1 : PP * T * 1 ≤ PP * T * Dd ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD1) e0
      have e2 : PP * T * Dd ^ 2 * 1 ≤ PP * T * Dd ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hU : (Fm.L x ι).sc.b ≤ unitE p := by
      rw [hW.unit]
      have e1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m := by nlinarith
      have e2 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x) := by
        have := mul_le_mul e1 (by linarith : (1 : ℝ) ≤ (Fm.L x ι).sc.L) zero_le_one (by linarith)
        have := mul_le_mul this hLL zero_le_one (by linarith)
        linarith
      have : (Fm.L x ι).sc.b * 1 ≤ (Fm.L x ι).sc.b *
          ((Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x)) :=
        mul_le_mul_of_nonneg_left e2 (by linarith)
      nlinarith
    have hPz : GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1)
        (Fm.D x ι).R.m 5 1 ≤ 200000 * zBase (Fm.L x ι) ^ 2 := hP.2
    calc (lenT p i (Fm.parT x hx ι).PP : ℝ) * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r
          ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1
        ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (200000 * (Fm.parT x hx ι).PP) :=
          mul_le_mul_of_nonneg_left (hPz.trans (by linarith)) hT0
      _ = 200000 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP) := by ring
      _ ≤ 200000 * unitE p := by linarith
  ·
    have hDF1 : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
    have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
    have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
      (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
    have key := size_inequality_real (Fm.D x ι).host.rdE (szCond (Fm.L x ι)) (Fm.D x ι).R.t (Fm.L x ι).sc.b (Fm.D x ι).R.f
      (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0) ((Fm.D x ι).host.g 1) h1 hc sC ht (by linarith) hft (by linarith) hrt
      hDF1 hDFb (hg 0) (hg 1)
    have hrun := GlobalTheory.RunParametersOfLower.runOK_of_le (Fm.D x ι).host.E (Fm.D x ι).R.r DF
      ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m hDF (by rw [ef]; nlinarith) (by omega) hm4 hf2 hrd16
      (by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; rw [ef, erd]; push_cast; exact key)
    rw [ef] at hrun
    exact hrun
  ·
    intro s hs
    have hR0 : (1 : ℝ) ≤ Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have : (0 : ℝ) ≤ DF := Nat.cast_nonneg _
      nlinarith
    have hRR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E) := by
      unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ (by linarith)
    have := sqrt_lt_th_real ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Y.d.l₂.M : ℝ)
      (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)))
      (ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E)) (Fm.L x ι).sc.b s hq1 hb0' (level_ge p i Y hY (by linarith))
      (by rw [ef]; linarith) hR0 hRR hs
    unfold ReciprocityTheory.ChartRestriction.G.I2.th
    exact this

end GlobalTheory.ThetaSizeBounds
end
