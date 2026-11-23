import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SubsingletonQuotientOfIdealEqTop
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParamsT
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.TwoFmLeRdE
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondLam
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm

theorem mono3 {f r l : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (a b c n : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (hc : c ≤ n) : f ^ a * r ^ b * l ^ c ≤ (f * r * l) ^ n := by
  have h1 : f ^ a ≤ f ^ n := pow_le_pow_right₀ hf ha
  have h2 : r ^ b ≤ r ^ n := pow_le_pow_right₀ hr hb
  have h3 : l ^ c ≤ l ^ n := pow_le_pow_right₀ hl hc
  have hf0 : 0 ≤ f ^ a := pow_nonneg (by linarith) a
  have hr0 : 0 ≤ r ^ b := pow_nonneg (by linarith) b
  have hl0 : 0 ≤ l ^ c := pow_nonneg (by linarith) c
  have hfn : 0 ≤ f ^ n := pow_nonneg (by linarith) n
  have hrn : 0 ≤ r ^ n := pow_nonneg (by linarith) n
  rw [mul_pow, mul_pow]
  exact mul_le_mul (mul_le_mul h1 h2 hr0 hfn) h3 hl0 (mul_nonneg hfn hrn)

variable {D : D7} {L : SizeData₂ D}

theorem f_eq (D : D7) : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
  simp only [Ranks.f]
  push_cast
  ring

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h : 1 ≤ D.R.n := by simp only [Ranks.n]; omega
  exact_mod_cast h

theorem two_le_f (D : D7) : (2 : ℝ) ≤ D.R.f := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h : 2 ≤ D.R.f := by simp only [Ranks.f, Ranks.n]; omega
  exact_mod_cast h

theorem six_le_r (D : D7) : (6 : ℝ) ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h : 6 ≤ D.R.r := by simp only [Ranks.r]; omega
  exact_mod_cast h

theorem m_le_r (D : D7) : (D.R.m : ℝ) ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h : D.R.m ≤ D.R.r := by simp only [Ranks.r]; omega
  exact_mod_cast h

theorem k_le_r (D : D7) : (D.R.k : ℝ) ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h : D.R.k ≤ D.R.r := by simp only [Ranks.r]; omega
  exact_mod_cast h

theorem r_le_two_k (D : D7) : (D.R.r : ℝ) ≤ 2 * D.R.k := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h : D.R.r ≤ 2 * D.R.k := by simp only [Ranks.r]; omega
  exact_mod_cast h

theorem r_le_alt_alt (D : D7) : (D.R.r : ℝ) ≤ D.R.t := by
  have h1 := D.R.rank_add_five_le
  have h : D.R.r ≤ D.R.t := by simp only [Ranks.r]; omega
  exact_mod_cast h

theorem two_le_m (D : D7) : (2 : ℝ) ≤ D.R.m := by
  exact_mod_cast D.R.two_le_m

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  simp only [Scale.L]
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem log_b (L : SizeData₂ D) : Real.log L.sc.b = L.sc.L := by
  simp only [Scale.b, Real.log_exp]

theorem condE_cast (D : D7) : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
  simp only [condE]
  push_cast
  ring

theorem one_le_q (D : D7) : (1 : ℝ) ≤ D.host.q := by
  exact_mod_cast D.host.hyp.1.one_lt.le

theorem one_le_d (D : D7) : (1 : ℝ) ≤ D.host.d := by
  exact_mod_cast D.host.hyp.2.1.one_lt.le

theorem one_le_qd (D : D7) : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := one_le_mul_of_one_le_of_one_le (one_le_q D) (one_le_d D)

theorem f_le_condE (D : D7) : (D.R.f : ℝ) ≤ (condE D : ℝ) := by
  have h : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
  have hN : 0 < D.host.QS * D.host.q * D.host.d :=
    Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos
  haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN.ne'⟩
  have hinj : Function.Injective D.host.cycEmb.toLinearMap := D.host.cycEmb.toRingHom.injective
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℚ (CyclotomicField (D.host.QS * D.host.q * D.host.d) ℚ) =
      Nat.totient (D.host.QS * D.host.q * D.host.d) :=
    IsCyclotomicExtension.finrank (CyclotomicField (D.host.QS * D.host.q * D.host.d) ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)
  have h3 := Nat.totient_le (D.host.QS * D.host.q * D.host.d)
  have h4 : D.R.f ≤ condE D := by
    simp only [condE, Ranks.f, Ranks.n]
    omega
  exact_mod_cast h4

theorem one_le_condE (D : D7) : (1 : ℝ) ≤ (condE D : ℝ) := by
  have h : 0 < condE D := by
    simp only [condE]
    exact Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos
  exact Nat.one_le_cast.mpr h

theorem log_cond_le (P : ParameterChoice' D L) :
    Real.log (condE D : ℝ) ≤ L.sc.L / 72 ∧ Real.log (D.R.t : ℝ) ≤ L.sc.L / 300 := by
  have hc := P.condE_le
  have h1 : (1 : ℝ) ≤ condE D := one_le_condE D
  have ht : (1 : ℝ) ≤ D.R.t := by
    have := r_le_alt_alt D
    have := six_le_r D
    linarith
  have hp1 : 0 < (condE D : ℝ) := by linarith
  have hp2 : 0 < (D.R.t : ℝ) := by linarith
  have hlog := Real.log_le_log (mul_pos (pow_pos hp1 36) (pow_pos hp2 150)) hc
  rw [Real.log_mul (pow_pos hp1 36).ne' (pow_pos hp2 150).ne', Real.log_pow, Real.log_pow] at hlog
  simp only [Scale.b] at hlog
  rw [Real.log_rpow (Real.exp_pos _), Real.log_exp] at hlog
  have hc0 : 0 ≤ Real.log (condE D : ℝ) := Real.log_nonneg h1
  have ht0 : 0 ≤ Real.log (D.R.t : ℝ) := Real.log_nonneg ht
  push_cast at hlog
  constructor <;> linarith

theorem log_f_le (P : ParameterChoice' D L) : Real.log (D.R.f : ℝ) ≤ L.sc.L / 72 := (Real.log_le_log (by linarith [two_le_f D]) (f_le_condE D)).trans (log_cond_le P).1

theorem log_r_le (P : ParameterChoice' D L) : Real.log (D.R.r : ℝ) ≤ L.sc.L / 300 := (Real.log_le_log (by linarith [six_le_r D]) (r_le_alt_alt D)).trans (log_cond_le P).2

theorem one_le_rdE (D : D7) : 1 ≤ D.host.rdE := by
  simp only [Host.rdE]
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
  exact_mod_cast h1

theorem log_rdE_nonneg (D : D7) : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (one_le_rdE D)

theorem x_le_fr (S : SizesAt L) : L.sc.x ≤ (D.R.f : ℝ) * D.R.r := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith)
  have h2 : L.sc.x ≤ (D.R.n : ℝ) := h1.trans S.1.1
  have h3 := six_le_r D
  have h4 := one_le_n D
  rw [f_eq]
  nlinarith

theorem fr_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  have hL := one_le_L L
  have h0 : 0 ≤ (D.R.f : ℝ) * D.R.r := by positivity
  exact le_mul_of_one_le_right h0 hL

theorem one_le_fr (D : D7) : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by
  have h1 := two_le_f D
  have h2 := six_le_r D
  nlinarith

theorem L_le_Z (L : SizeData₂ D) : L.sc.L ≤ zBase L := by
  have h1 := one_le_fr D
  have h2 := one_le_L L
  show L.sc.L ≤ (D.R.f : ℝ) * D.R.r * L.sc.L
  nlinarith

theorem Z_ge (S : SizesAt L) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : (10 : ℝ) ^ 60 ≤ zBase L := le_trans hx (le_trans (x_le_fr S) (fr_le_Z L))

theorem mono (L : SizeData₂ D) (a b c n : ℕ) (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) :
    (D.R.f : ℝ) ^ a * (D.R.r : ℝ) ^ b * L.sc.L ^ c ≤ zBase L ^ n := by
  have h := mono3 (f := (D.R.f : ℝ)) (r := (D.R.r : ℝ)) (l := L.sc.L) (by linarith [two_le_f D])
    (by linarith [six_le_r D]) (one_le_L L) a b c n ha hb hc
  exact h

theorem fr_le_pow (S : SizesAt L) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : (D.R.f : ℝ) * D.R.r ≤ L.sc.x ^ (20 : ℝ) := by
  have hx1 := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (by norm_num) hx
  have e3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast L.sc.x 3
  have e5 : L.sc.x ^ (5 : ℝ) = L.sc.x ^ (5 : ℕ) := by exact_mod_cast Real.rpow_natCast L.sc.x 5
  have e20 : L.sc.x ^ (20 : ℝ) = L.sc.x ^ (20 : ℕ) := by exact_mod_cast Real.rpow_natCast L.sc.x 20
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℕ) := by
    rw [← e3]
    exact S.1.2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℕ) := by
    rw [← e5]
    exact S.2.2.1.2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by unfold szTh; linarith))
  have hx0 : 0 ≤ L.sc.x := by linarith
  rw [e20, f_eq]
  calc 2 * (D.R.n : ℝ) * D.R.r ≤ 2 * (D.R.n : ℝ) * (2 * D.R.k) :=
        mul_le_mul_of_nonneg_left (r_le_two_k D) (by positivity)
    _ = 4 * ((D.R.n : ℝ) * D.R.k) := by ring
    _ ≤ 4 * (L.sc.x ^ (3 : ℕ) * L.sc.x ^ (5 : ℕ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hn hk (by positivity) (by positivity)) (by norm_num)
    _ ≤ L.sc.x * (L.sc.x ^ (3 : ℕ) * L.sc.x ^ (5 : ℕ)) := mul_le_mul_of_nonneg_right hx4 (by positivity)
    _ = L.sc.x ^ (9 : ℕ) := by ring
    _ ≤ L.sc.x ^ (20 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)

theorem logOm_le (P : ParameterChoice' D L) : |L.logOm| ≤ 6 * L.sc.L := by
  have hL := one_le_L L
  have h1 := log_rdE_le_scL P
  have h0 := log_rdE_nonneg D
  have hrd : 0 < D.host.rdE := by linarith [one_le_rdE D]
  have hd := P.logDerivative_le_power
  have hdL : L.sc.x ^ L.sc.eps = L.sc.L := rfl
  rw [hdL] at hd
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  have hg0 : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant; linarith
  have hg1 : Real.eulerMascheroniConstant < 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi1 : Real.log Real.pi ≤ 2 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_le_four
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have e : Real.log (Real.pi / D.host.v) = Real.log Real.pi - Real.log D.host.rdE + Real.log 2 := by
    unfold Host.v
    rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_div hrd.ne' (by norm_num)]
    ring
  unfold SizeData₂.logOm
  rw [e, abs_le]
  constructor <;> linarith

theorem two_fm_le_rdE (D : D7) : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE :=
  (UpperTheory.Ram.two_fm_le_rdE D.R D.host).1

theorem parA_of (P : ParameterChoice' D L) (S : SizesAt L) (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1)
    (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) : ParA L 20 := by
  have hL := one_le_L L
  refine ⟨x_le_fr S, fr_le_pow S hx, ?_, S.2.2.2.2.2.2.2.2.2.2.2.1, hg, P.logDerivative_le_power, ?_, P.pde_log.1, P.pde_log.2,
    two_fm_le_rdE D⟩
  · have h := logdE_le_two_f_L P
    have h6 := six_le_r D
    have hf : (0 : ℝ) ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    have e : (20 : ℝ) * ((D.R.f : ℝ) * D.R.r * L.sc.L) = 20 * D.R.r * ((D.R.f : ℝ) * L.sc.L) := by ring
    show logdE D ≤ _
    rw [e]
    nlinarith
  · exact (logOm_le P).trans (by linarith)

theorem one_le_Z (L : SizeData₂ D) : 1 ≤ zBase L := one_le_mul_of_one_le_of_one_le (one_le_fr D) (one_le_L L)

theorem Zpow_le (L : SizeData₂ D) {a n : ℕ} (h : a ≤ n) : zBase L ^ a ≤ zBase L ^ n := pow_le_pow_right₀ (one_le_Z L) h

theorem PO_le (L : SizeData₂ D) : PO D L ≤ 217 * zBase L ^ 2 := by
  have hf : (2 : ℝ) ≤ D.R.f := two_le_f D
  have hr : (6 : ℝ) ≤ D.R.r := six_le_r D
  have hL : 1 ≤ L.sc.L := one_le_L L
  have hfL : 1 ≤ (D.R.f : ℝ) * L.sc.L := by nlinarith
  have hrL : 1 ≤ (D.R.r : ℝ) ^ 2 * L.sc.L := by nlinarith
  have hA : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L := by positivity
  have hB : 0 ≤ (D.R.f : ℝ) ^ 2 * L.sc.L := by positivity
  have h1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ≤ ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 :=
    calc (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L
        ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L * ((D.R.f : ℝ) * L.sc.L) := le_mul_of_one_le_right hA hfL
      _ = ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 := by ring
  have h2 : (D.R.f : ℝ) ^ 2 * L.sc.L ≤ ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 :=
    calc (D.R.f : ℝ) ^ 2 * L.sc.L
        ≤ (D.R.f : ℝ) ^ 2 * L.sc.L * ((D.R.r : ℝ) ^ 2 * L.sc.L) := le_mul_of_one_le_right hB hrL
      _ = ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 := by ring
  simp only [WeightAlgebra.PO]
  show 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L + 198 * (D.R.f : ℝ) ^ 2 * L.sc.L ≤
    217 * ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2
  linarith

theorem log_g_sum (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) :
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 18 * L.sc.L + 2 := by
  have hL := one_le_L L
  have h0 := hg 0
  have h1 := hg 1
  by_cases ha : (D.host.g 0 : ℝ) = 0
  · rw [ha, zero_mul, Real.log_zero]
    linarith
  by_cases hb : (D.host.g 1 : ℝ) = 0
  · rw [hb, mul_zero, Real.log_zero]
    linarith
  rw [Real.log_mul ha hb]
  linarith

theorem lamStar_le (P : ParameterChoice' D L) (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) :
    lamStar D ≤ 21 * L.sc.L := by
  have hL := one_le_L L
  have hn := one_le_n D
  have hq := one_le_q D
  have hd := one_le_d D
  have hqd := one_le_qd D
  have hc0 : (0 : ℝ) < (condE D : ℝ) := by linarith [one_le_condE D]
  have e1 : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d = 4 * (D.R.n : ℝ) ^ 2 * D.host.q * D.host.d := by
    rw [f_eq]; ring
  have hpos : 0 < 4 * (D.R.n : ℝ) ^ 2 * D.host.q * D.host.d := by positivity
  have h2 : 4 * (D.R.n : ℝ) ^ 2 * D.host.q * D.host.d ≤ (condE D : ℝ) ^ 2 := by
    rw [condE_cast, ← e1]
    exact (UpperTheory.Ram.cond_le_four_n_sq D.R D.host).2.1
  have h3 := Real.log_le_log hpos h2
  rw [Real.log_pow] at h3
  have h4 := (log_cond_le P).1
  have h5 := log_g_sum hg
  unfold lamStar
  rw [e1]
  push_cast at h3
  linarith

theorem log_qdg_le (P : ParameterChoice' D L) (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) :
    Real.log (D.host.QS * (D.host.q : ℝ) * D.host.d * D.host.g 0 * D.host.g 1) ≤ 21 * L.sc.L := by
  have hL := one_le_L L
  have hn := one_le_n D
  have hq := one_le_q D
  have hd := one_le_d D
  have hqd := one_le_qd D
  have g0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
  have g1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
  have hQ := UpperTheory.Ram.Rd.one_le_QS_real D.host
  have hpos : 0 < D.host.QS * (D.host.q : ℝ) * D.host.d := by positivity
  have e : D.host.QS * (D.host.q : ℝ) * D.host.d * D.host.g 0 * D.host.g 1 =
      (D.host.QS * (D.host.q : ℝ) * D.host.d) * ((D.host.g 0 : ℝ) * D.host.g 1) := by ring
  have h2 : D.host.QS * (D.host.q : ℝ) * D.host.d ≤ (condE D : ℝ) := (condE_cast D).ge
  have h3 := Real.log_le_log hpos h2
  have h4 := (log_cond_le P).1
  have h5 := log_g_sum hg
  rw [e, Real.log_mul hpos.ne' (mul_pos g0 g1).ne']
  linarith

theorem lrd_eq (D : D7) : lrd D = Real.log D.host.rdE := by
  have hfr : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    have h : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
    rw [h]
    simp only [Ranks.f, Ranks.n]
    push_cast
    ring
  have hd : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
  simp only [WeightAlgebra.lrd, Host.rdE]
  rw [Real.log_rpow hd, hfr]
  ring

theorem PU_le (P : ParameterChoice' D L) : PU D ≤ 7 * zBase L := by
  have hL := one_le_L L
  have hf0 : (0 : ℝ) < D.R.f := by linarith [two_le_f D]
  have hr0 : (0 : ℝ) < D.R.r := by linarith [six_le_r D]
  have h1 := log_rdE_le_scL P
  have h2 := log_f_le P
  have h3 := log_r_le P
  unfold PU zBase
  rw [lrd_eq, Real.log_mul hf0.ne' hr0.ne']
  have h4 : 2 * Real.log D.host.rdE + 2 * (Real.log (D.R.f : ℝ) + Real.log (D.R.r : ℝ)) + 3 ≤ 7 * L.sc.L := by linarith
  calc (D.R.f : ℝ) * D.R.r * (2 * Real.log D.host.rdE + 2 * (Real.log (D.R.f : ℝ) + Real.log (D.R.r : ℝ)) + 3)
      ≤ (D.R.f : ℝ) * D.R.r * (7 * L.sc.L) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem sigW_m (D : D7) : D.R.sigW D.R.m = (D.R.r, 0) := by
  unfold Ranks.sigW Ranks.r; rw [Nat.sub_self]

theorem baseDegree_at_lift_index (D : D7) : n0 D D.R.m = D.R.r + 2 * g0 D := by
  unfold n0; rw [sigW_m]; simp

theorem genusConstant_cast (D : D7) : (g0 D : ℝ) = 1250 * (D.R.r : ℝ) := by unfold g0; push_cast; ring

theorem dimY_m_le (D : D7) : (WeightFamilies.dimY D D.R.m : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by
  have h : WeightFamilies.dimY D D.R.m ≤ D.R.f * D.R.r ^ 2 := by
    unfold WeightFamilies.dimY
    rw [sigW_m]
    apply Nat.mul_le_mul_left
    simp only [mul_zero, zero_mul, Nat.zero_div, add_zero, zero_add]
    calc D.R.r * (D.R.r - 1) / 2 ≤ D.R.r * (D.R.r - 1) := Nat.div_le_self _ _
      _ ≤ D.R.r * D.R.r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = D.R.r ^ 2 := (sq _).symm
  exact_mod_cast h

theorem nW_le_Z (P : ParameterChoice' D L) (T : ParamsT D L P) (hCnW : P.CnW = 10) : (T.nWn : ℝ) ≤ 28 * zBase L ^ 4 := by
  have hL := one_le_L L
  have hf := two_le_f D
  have hr := six_le_r D
  have hm := two_le_m D
  have hk1 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
    have : 1 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast this
    linarith
  have hk2 : (D.R.k : ℝ) - 1 ≤ D.R.r := by linarith [k_le_r D]
  have hk3 : ((D.R.k : ℝ) - 1) ^ 3 ≤ (D.R.r : ℝ) ^ 3 := pow_le_pow_left₀ hk1 hk2 3
  have h := T.nW_win.2.le
  rw [hCnW] at h
  unfold nW at h
  have a1 : (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m ≤
      (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 3 * L.sc.L ^ 2 := by
    refine (div_le_self (by positivity) (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk3 (by positivity)) (by positivity)
  have a2 : 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) ≤
      10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 3 * L.sc.L ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have m1 := mono L 1 1 0 4 (by norm_num) (by norm_num) (by norm_num)
  have m2 := mono L 2 4 2 4 (by norm_num) (by norm_num) (by norm_num)
  have m3 := mono L 0 0 0 4 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at m1 m2 m3
  have e : 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 3 * L.sc.L ^ 2) =
      10 * ((D.R.f : ℝ) * D.R.r) + 10 * ((D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 * L.sc.L ^ 2) := by ring
  rw [e] at a2
  linarith

theorem polyConstant_le_zBase_pow_four (P : ParameterChoice' D L) (T : ParamsT D L P) (hCnW : P.CnW = 10) :
    sizeConstantAtParamsWeight D T.nWn ≤ 1000 * zBase L ^ 4 := by
  have hL := one_le_L L
  have hf := two_le_f D
  have hr := six_le_r D
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have m0 := mono L 0 0 0 4 (by norm_num) (by norm_num) (by norm_num)
  have m1 := mono L 1 1 0 4 (by norm_num) (by norm_num) (by norm_num)
  have m2 := mono L 1 3 0 4 (by norm_num) (by norm_num) (by norm_num)
  have m3 := mono L 0 1 1 4 (by norm_num) (by norm_num) (by norm_num)
  have m4 := mono L 0 1 0 4 (by norm_num) (by norm_num) (by norm_num)
  have m5 := mono L 1 2 0 4 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one, one_mul] at m0 m1 m2 m3 m4 m5
  unfold sizeConstantAtParamsWeight
  refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
  · linarith
  · have : (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 3 := pow_le_pow_left₀ hm0 (m_le_r D) 3
    have h2 : 360 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ 360 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have e : 360 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 = 360 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 3) := by ring
    linarith
  · have h1 : Real.log (D.R.r : ℝ) ≤ L.sc.L := (log_r_le P).trans (by linarith)
    have h2 : (D.R.r : ℝ) * Real.log (D.R.r : ℝ) ≤ (D.R.r : ℝ) * L.sc.L :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  · linarith [nW_le_Z P T hCnW]
  · rw [genusConstant_cast]
    have : (D.R.r : ℝ) * 2 ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    linarith
  · linarith
  · linarith

theorem liftConstant_le_zBase_pow_ten (L : SizeData₂ D) : DivisibilityWeightConstant D D.R.m ≤ 1000 * zBase L ^ 10 := by
  have hf := two_le_f D
  have hr := six_le_r D
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (WeightFamilies.dimY D D.R.m : ℝ) := Nat.cast_nonneg _
  have h1 : (WeightFamilies.dimY D D.R.m : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hD0 (dimY_m_le D) 2
  have h2 : (D.R.m : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 4 := pow_le_pow_left₀ hm0 (m_le_r D) 4
  have h6 : (64 : ℝ) ≤ (D.R.f : ℝ) ^ 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hf 6
  have m1 := mono L 10 10 0 10 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one] at m1
  unfold DivisibilityWeightConstant
  calc 72 * 5 ^ 4 * (WeightFamilies.dimY D D.R.m : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * (D.R.m : ℝ) ^ 4
      = 45000 * ((WeightFamilies.dimY D D.R.m : ℝ) ^ 2 * (D.R.m : ℝ) ^ 4) * ((D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2) := by ring
    _ ≤ 45000 * (((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2) ^ 2 * (D.R.r : ℝ) ^ 4) * ((D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity))
          (by norm_num)) (by positivity)
    _ = 45000 * ((D.R.f : ℝ) ^ 4 * (D.R.r : ℝ) ^ 10) := by ring
    _ ≤ 1000 * (64 * ((D.R.f : ℝ) ^ 4 * (D.R.r : ℝ) ^ 10)) := by
        have : 0 ≤ (D.R.f : ℝ) ^ 4 * (D.R.r : ℝ) ^ 10 := by positivity
        linarith
    _ ≤ 1000 * ((D.R.f : ℝ) ^ 6 * ((D.R.f : ℝ) ^ 4 * (D.R.r : ℝ) ^ 10)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 (by positivity)) (by norm_num)
    _ = 1000 * ((D.R.f : ℝ) ^ 10 * (D.R.r : ℝ) ^ 10) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left m1 (by norm_num)

theorem domAt_of (P : ParameterChoice' D L) (T : ParamsT D L P) (S : SizesAt L) (hCnW : P.CnW = 10)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x) :
    DomAt D L D.R.m T.nWn 1000 := by
  have hL := one_le_L L
  have hLZ := L_le_Z L
  have hZ := Z_ge S hx
  have hZ1 := one_le_Z L
  have eZ : Zb D L = zBase L := rfl
  unfold DomAt
  rw [eZ]
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, polyConstant_le_zBase_pow_four P T hCnW, liftConstant_le_zBase_pow_ten L⟩
  · calc (1000 : ℝ) ^ 20 = 10 ^ 60 := by norm_num
      _ ≤ _ := hZ
  · linarith [lamStar_le P hg]
  · unfold PN; linarith [lamStar_le P hg]
  · have ec : (D.host.condN : ℝ) = D.host.QS * (D.host.q : ℝ) * D.host.d := condE_cast D
    rw [ec]
    linarith [log_qdg_le P hg]
  · linarith [PU_le P]
  · have := PO_le L
    have h0 : 0 ≤ zBase L ^ 2 := by positivity
    linarith
  · rw [baseDegree_at_lift_index]
    push_cast
    rw [genusConstant_cast]
    have m1 := mono L 0 1 0 2 (by norm_num) (by norm_num) (by norm_num)
    simp only [pow_one, pow_zero, mul_one, one_mul] at m1
    have h3 : (3 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
    have h0 : 0 ≤ zBase L ^ 2 := by positivity
    have e : zBase L ^ 3 = zBase L * zBase L ^ 2 := by ring
    rw [e]
    nlinarith

theorem finrank_E (D : D7) : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
  have h : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
  rw [h]
  simp only [Ranks.f, Ranks.n]
  push_cast
  ring

theorem log_two_f_le (L : SizeData₂ D) : Real.log (2 * (D.R.f : ℝ)) ≤ zBase L := by
  have hf := two_le_f D
  have hr := six_le_r D
  have hL := one_le_L L
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * (D.R.f : ℝ) by linarith)
  have h2 : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * L.sc.L :=
    le_mul_of_one_le_right (by positivity) hL
  have h3 : 6 * (D.R.f : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  show Real.log (2 * (D.R.f : ℝ)) ≤ (D.R.f : ℝ) * D.R.r * L.sc.L
  linarith

theorem opo_of (P : ParameterChoice' D L) (e : 𝓞 D.host.E ≃+* D.what₂.O) (Sg : ∀ j, WeightFamilies.Wt D j → Prop) :
    OPO L (Inh.provS D D.host.E e Sg) := by
  have hL := one_le_L L
  have hf := two_le_f D
  have hr := six_le_r D
  have hPO : zBase L ≤ PO D L := by
    unfold PO zBase
    have a1 : (D.R.f : ℝ) * D.R.r * L.sc.L ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L := by
      have : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by linarith)) (by linarith)
    have a2 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L := by positivity
    have a3 : 0 ≤ 198 * (D.R.f : ℝ) ^ 2 * L.sc.L := by positivity
    have e1 : 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L = 19 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L) := by ring
    rw [e1]
    linarith
  constructor
  · show Real.log (Module.finrank ℚ D.host.E : ℝ) ≤ _
    rw [finrank_E]
    exact (log_two_f_le L).trans hPO
  · show Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / (Module.finrank ℚ D.host.E : ℝ) ≤ _
    rw [finrank_E]
    have h := lrd_eq D
    unfold lrd at h
    rw [h]
    exact (log_rdE_le_scL P).trans ((L_le_Z L).trans hPO)

theorem Z_le_rpow_two (L : SizeData₂ D) : zBase L ≤ WeightFamilies.PPv D L 1 2 := by
  have h := one_le_Z L
  simp only [WeightFamilies.PPv, one_mul]
  rw [Real.rpow_two]
  nlinarith

theorem obound_of (P : ParameterChoice' D L) (e : 𝓞 D.host.E ≃+* D.what₂.O) (Sg : ∀ j, WeightFamilies.Wt D j → Prop) :
    WeightFamilies.Obound (Inh.provS D D.host.E e Sg) L 1 2 := by
  constructor
  · show Real.log (Module.finrank ℚ D.host.E : ℝ) ≤ _
    rw [finrank_E]
    exact (log_two_f_le L).trans (Z_le_rpow_two L)
  · show Real.log (|((NumberField.discr D.host.E : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ))) ≤ _
    have : |((NumberField.discr D.host.E : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
    rw [this]
    exact (log_rdE_le_scL P).trans ((L_le_Z L).trans (Z_le_rpow_two L))

theorem growthZero_le_thirty_zBase (P : ParameterChoice' D L) : WeightFamilies.PP0v D L 1 1 ≤ 30 * zBase L := by
  have hL := one_le_L L
  have hr := six_le_r D
  have h1 := fr_le_Z L
  have h2 := L_le_Z L
  have h3 := logdE_le_two_f_L P
  have h4 := logOm_le P
  have h5 : 2 * (D.R.f : ℝ) * L.sc.L ≤ zBase L := by
    unfold zBase
    have : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
    nlinarith
  unfold WeightFamilies.PP0v
  rw [Real.rpow_one, one_mul]
  linarith

theorem growthZero_nonneg (L : SizeData₂ D) : 0 ≤ WeightFamilies.PP0v D L 1 1 := by
  have h3 : 0 ≤ logdE D := by
    rw [logdE_eq_rd]; have := log_rdE_nonneg D; positivity
  have hL := one_le_L L
  unfold WeightFamilies.PP0v
  rw [Real.rpow_one, one_mul]
  have : 0 ≤ (D.R.f : ℝ) * D.R.r := by positivity
  have := abs_nonneg L.logOm
  linarith

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

alias parA_of := Pm.parA_of
alias domAt_of := Pm.domAt_of
alias opo_of := Pm.opo_of
alias obound_of := Pm.obound_of
alias growthZero_le_thirty_zBase := Pm.growthZero_le_thirty_zBase
alias growthZero_nonneg := Pm.growthZero_nonneg
alias PO_le := Pm.PO_le

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
