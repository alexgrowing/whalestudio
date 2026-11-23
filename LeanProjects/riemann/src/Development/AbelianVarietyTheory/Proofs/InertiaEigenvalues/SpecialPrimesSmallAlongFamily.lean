import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.SpecialSmall

open Filter Real

theorem ev_pow_le_exp {eps : ℝ} (he : 0 < eps) (K s : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * x ^ s ≤ Real.exp (x ^ eps) := by
  have h1 := (tendsto_exp_div_rpow_atTop (s / eps)).comp (tendsto_rpow_atTop he)
  filter_upwards [h1.eventually_ge_atTop K, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  simp only [Function.comp] at hx
  have hxs : (x ^ eps) ^ (s / eps) = x ^ s := by
    rw [← Real.rpow_mul hx0.le]; congr 1; field_simp
  rw [hxs] at hx
  have hpos : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
  rwa [le_div_iff₀ hpos] at hx

theorem midG_alg (C f r m b l S t η large₂ P : ℝ) (hC : 0 ≤ C) (hf : 1 ≤ f) (hm : 1 ≤ m) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hl : 2 * r ≤ l) (hl0 : 0 < l) (hX : r * (S + t + η + large₂) ≤ m * b / 4)
    (hP : P * large₂ ≤ b / 4) :
    C * f * (r * (b / l + S + t + η + large₂) + m * b) + C * P * large₂ ≤ 2 * C * f * m * b := by
  have h1 : r * (b / l) ≤ b / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hl0 two_pos]; nlinarith
  have h2 : r * (b / l + S + t + η + large₂) ≤ m * b * (3 / 4) := by
    have : r * (b / l + S + t + η + large₂) = r * (b / l) + r * (S + t + η + large₂) := by ring
    nlinarith
  have hCf : 0 ≤ C * f := by positivity
  have h3 : C * f * (r * (b / l + S + t + η + large₂) + m * b) ≤ C * f * (m * b * (7 / 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCf
  have hfm : b / 4 ≤ f * m * b / 4 := by
    have : 1 ≤ f * m := by nlinarith
    have : b ≤ f * m * b := by nlinarith
    linarith
  have h4 : C * P * large₂ ≤ C * (f * m * b / 4) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hP.trans hfm) hC
  nlinarith

open Formalism.MainNotions.TwistedPlaces in

theorem not_inert_three {D : D7} (h : 3 ≤ D.host.splitBound) : ¬ TwistedPlaces.InertK D 3 := by
  have hj := D.host.split_small 3 Nat.prime_three (by norm_num) h
  have hq : (3 : ℕ) ≠ D.host.q := fun e => D.host.q_ne_three e.symm
  have hd21 : (21 : ℝ) < D.host.d := by
    have h := D.host.qd_big.2
    have h' : (4 * D.R.t * D.R.r + 1 : ℝ) < D.host.d := by exact_mod_cast h
    have := t_ge_one D; have := k_le_r D; have := k_ge_five D
    nlinarith
  have hd : (3 : ℕ) ≠ D.host.d := by
    intro e; rw [← e] at hd21; norm_num at hd21
  unfold TwistedPlaces.InertK
  simp only [Host.cls, primeClass]
  by_cases h3 : 3 ∈ D.host.small
  · rw [if_pos h3]
    simp
  · rw [if_neg h3, if_neg hq, if_neg hd, if_pos hj]
    simp

open Formalism.MainNotions.TwistedPlaces in

theorem qd_le_lStar {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    (D.host.q : ℝ) ≤ TwistedPlaces.lStar L ∧ (D.host.d : ℝ) ≤ TwistedPlaces.lStar L ∧
      ∀ l ∈ D.host.small, (l : ℝ) ≤ TwistedPlaces.lStar L := by
  have hl1 : L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L := P.lstar1
  have hpos := lStar_pos L
  have hb' := b'_pos L; have := L.Sc_pos; have := L.etaSz_pos
  have hbl : L.sc.b ≤ lStar L ^ 2 := by
    have : L.sc.b / lStar L < lStar L := by linarith
    rw [div_lt_iff₀ hpos] at this; nlinarith
  have hsq : Real.sqrt L.sc.b ≤ lStar L := by
    have := Real.sqrt_le_sqrt hbl
    rwa [Real.sqrt_sq hpos.le] at this
  have hc := P.condE_le
  rw [← Real.sqrt_eq_rpow] at hc
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1; exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2; exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hpos' : 0 < LevelStarExponents.condE D :=
    Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos
  have hqE : (D.host.q : ℝ) ≤ LevelStarExponents.condE D := by
    exact_mod_cast Nat.le_of_dvd hpos' ((dvd_mul_left _ _).mul_right _)
  have hdE : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by
    exact_mod_cast Nat.le_of_dvd hpos' (dvd_mul_left _ _)
  have hsE : ∀ l ∈ D.host.small, (l : ℝ) ≤ LevelStarExponents.condE D := fun l hl => by
    exact_mod_cast Nat.le_of_dvd hpos' (((Nat.dvd_of_mem_primeFactors hl).mul_right _).mul_right _)
  have hE1 : 1 ≤ (LevelStarExponents.condE D : ℝ) := hq1.trans hqE
  have hE36 : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := le_self_pow₀ hE1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ (t_ge_one D)
  have hE : (LevelStarExponents.condE D : ℝ) ≤ lStar L := by
    have : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 := by
      have : 0 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by positivity
      nlinarith
    linarith
  exact ⟨hqE.trans hE, hdE.trans hE, fun l hl => (hsE l hl).trans hE⟩

end GlobalTheory.SpecialSmall

noncomputable section

namespace GlobalTheory.SpecialSmall

open Filter Real Formalism.MainNotions.TwistedPlaces

theorem at_one {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (hS : SizesAt L) (C : ℝ) (hC : 1 ≤ C)
    (h3 : 3 ≤ L.sc.x) (h16 : max 16 C ≤ L.sc.x ^ L.sc.eps) (h60 : 60 ≤ L.sc.x ^ (L.sc.ez / 5))
    (hbig : 4 * 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C + L.sc.eps) ≤ Real.exp (L.sc.x ^ L.sc.eps))
    (hbig2 : 32 * L.sc.x ^ (5 + L.sc.eps) ≤ Real.exp (L.sc.x ^ L.sc.eps)) :
    Small L C ∧ 8 ≤ L.sc.L ∧ 60 ≤ D.host.splitBound ∧ C ≤ L.sc.b := by
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hLg : large₂ L = L.sc.x ^ L.sc.eps := rfl
  have hbe : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have h16' : 16 ≤ L.sc.x ^ L.sc.eps := (le_max_left _ _).trans h16
  have hCx : C ≤ L.sc.x ^ L.sc.eps := (le_max_right _ _).trans h16

  have hsb : 60 ≤ D.host.splitBound := by
    refine le_trans ?_ L.split_tie
    exact Nat.le_floor (by exact_mod_cast h60)

  have hK := hS.2.2.1.2
  have hT := hS.2.2.2.2.1.2
  unfold Formalism.MainNotions.szTh at hK hT
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) :=
    hK.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have ht1 : (D.R.t : ℝ) ≤ L.sc.x ^ (|L.Ct| + 1) :=
    hT.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by have := le_abs_self L.Ct; linarith))
  have hf := f_le_k D
  have hr := r_le_two_k D
  have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hf1 : (1 : ℝ) ≤ D.R.f := by rw [f_eq]; linarith [n_ge_one D]
  have hm1 := m_ge_one D
  have ht0 := t_ge_one D
  have hx5 : 0 ≤ L.sc.x ^ (5 : ℝ) := by positivity

  have hfrt : (D.R.f : ℝ) * D.R.r * D.R.t ≤ 2 * L.sc.x ^ (11 + |L.Ct|) := by
    have e : L.sc.x ^ (11 + |L.Ct|) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ (5 : ℝ) * L.sc.x ^ (|L.Ct| + 1) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    rw [e]
    have h1 : (D.R.f : ℝ) * D.R.r ≤ L.sc.x ^ (5 : ℝ) * (2 * L.sc.x ^ (5 : ℝ)) :=
      mul_le_mul (hf.trans hk5) (hr.trans (by linarith)) hr0 hx5
    calc (D.R.f : ℝ) * D.R.r * D.R.t ≤ (L.sc.x ^ (5 : ℝ) * (2 * L.sc.x ^ (5 : ℝ))) * L.sc.x ^ (|L.Ct| + 1) :=
          mul_le_mul h1 ht1 (by linarith) (by positivity)
      _ = 2 * (L.sc.x ^ (5 : ℝ) * L.sc.x ^ (5 : ℝ) * L.sc.x ^ (|L.Ct| + 1)) := by ring

  have hP : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C * large₂ L ≤ L.sc.b / 4 := by
    have hfrt0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by positivity
    have h1 : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C ≤ 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C) := by
      calc ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C ≤ (2 * L.sc.x ^ (11 + |L.Ct|)) ^ C :=
            Real.rpow_le_rpow hfrt0 hfrt (by linarith)
        _ = 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
    have h2 : 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C) * L.sc.x ^ L.sc.eps =
        2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C + L.sc.eps) := by
      rw [Real.rpow_add hx0]; ring
    have hL0 : 0 ≤ large₂ L := Lg_nonneg L
    calc ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C * large₂ L ≤ 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C) * large₂ L :=
          mul_le_mul_of_nonneg_right h1 hL0
      _ = 2 ^ C * L.sc.x ^ ((11 + |L.Ct|) * C + L.sc.eps) := by rw [hLg, h2]
      _ ≤ L.sc.b / 4 := by rw [hbe]; linarith

  have hlog : 1 ≤ Real.log L.sc.x := by
    have : Real.exp 1 ≤ L.sc.x := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log L.sc.x := Real.log_le_log (Real.exp_pos 1) this
  have hb'0 := b'_pos L
  have hrb' : 16 * (D.R.r * L.sc.b') ≤ D.R.m * L.sc.b := by
    have hA := lA_ge L
    have h16A : 16 ≤ lA L * Real.log L.sc.x := by
      have : 16 ≤ lA L := by rw [hLg] at hA; linarith
      calc (16 : ℝ) = 16 * 1 := by norm_num
        _ ≤ lA L * Real.log L.sc.x := mul_le_mul this hlog (by norm_num) (by linarith)
    have := rb'lA_le L P
    calc 16 * (D.R.r * L.sc.b') ≤ (lA L * Real.log L.sc.x) * (D.R.r * L.sc.b') :=
          mul_le_mul_of_nonneg_right h16A (by positivity)
      _ = D.R.r * L.sc.b' * lA L * Real.log L.sc.x := by ring
      _ ≤ D.R.m * L.sc.b := this

  have hb0 : 0 ≤ L.sc.b := by rw [hbe]; positivity
  have hrL : 16 * (D.R.r * large₂ L) ≤ D.R.m * L.sc.b := by
    have hr5 : (D.R.r : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by linarith
    have e : L.sc.x ^ (5 + L.sc.eps) = L.sc.x ^ (5 : ℝ) * L.sc.x ^ L.sc.eps := Real.rpow_add hx0 _ _
    have : 16 * (D.R.r * large₂ L) ≤ 32 * L.sc.x ^ (5 + L.sc.eps) := by
      rw [e, hLg]
      have := mul_le_mul_of_nonneg_right hr5 (by positivity : (0 : ℝ) ≤ L.sc.x ^ L.sc.eps)
      linarith
    have : L.sc.b ≤ D.R.m * L.sc.b := le_mul_of_one_le_left hb0 hm1
    have : 32 * L.sc.x ^ (5 + L.sc.eps) ≤ L.sc.b := by rw [hbe]; exact hbig2
    linarith

  have hSb := S_le_b' L P
  have heb := eta_le_b' L P
  have htb := (t_le_eta L P).trans heb
  have hX : (D.R.r : ℝ) * (L.Sc + D.R.t + L.etaSz + large₂ L) ≤ D.R.m * L.sc.b / 4 := by
    have : (D.R.r : ℝ) * (L.Sc + D.R.t + L.etaSz) ≤ D.R.r * (3 * L.sc.b') :=
      mul_le_mul_of_nonneg_left (by linarith) hr0
    have e : (D.R.r : ℝ) * (L.Sc + D.R.t + L.etaSz + large₂ L) = D.R.r * (L.Sc + D.R.t + L.etaSz) + D.R.r * large₂ L := by ring
    rw [e]; linarith

  have hl2r : ∀ l : ℕ, (l = D.host.q ∨ l = D.host.d) → 2 * (D.R.r : ℝ) ≤ l ∧ (0 : ℝ) < l := by
    intro l hl
    have h : 4 * D.R.t * D.R.r + 1 < l := by
      rcases hl with rfl | rfl
      · exact D.host.qd_big.1
      · exact D.host.qd_big.2
    have h' : (4 * D.R.t * D.R.r + 1 : ℝ) < l := by exact_mod_cast h
    have h4 : (0 : ℝ) ≤ 4 * D.R.t * D.R.r := by positivity
    have h5 : (D.R.r : ℝ) ≤ D.R.t * D.R.r := le_mul_of_one_le_left hr0 ht0
    constructor
    · linarith
    · linarith
  have hsmall : Small L C := by
    obtain ⟨hq, hd, hsl⟩ := qd_le_lStar L P
    refine ⟨by linarith [seven_lt_lStar L P], hq, hd, not_inert_three (by omega), ?_, hsl⟩
    intro l hl
    obtain ⟨h2r, hl0⟩ := hl2r l hl
    unfold midG
    exact midG_alg C D.R.f D.R.r D.R.m L.sc.b l L.Sc D.R.t L.etaSz (large₂ L)
      (((D.R.f : ℝ) * D.R.r * D.R.t) ^ C) (by linarith) hf1 hm1 hb0 hr0 h2r hl0 hX hP
  refine ⟨hsmall, ?_, hsb, ?_⟩
  · show 8 ≤ L.sc.x ^ L.sc.eps; linarith
  · rw [hbe]; linarith [Real.add_one_le_exp (L.sc.x ^ L.sc.eps)]

end GlobalTheory.SpecialSmall

open Filter in

theorem GlobalTheory.SpecialSmall.special_primes_small : ∀ {eps : ℝ} (Fm : FamP eps), ∀ C : ℝ, 1 ≤ C → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Small (Fm.L x i) C ∧ 8 ≤ (Fm.L x i).sc.L ∧ 60 ≤ (Fm.D x i).host.splitBound ∧ C ≤ (Fm.L x i).sc.b := by
  intro eps Fm C hC
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.one_le_J)
  have ev1 : ∀ᶠ x : ℝ in atTop, (3 : ℝ) ≤ x := eventually_ge_atTop 3
  have ev2 : ∀ᶠ x : ℝ in atTop, max 16 C ≤ x ^ eps := (tendsto_rpow_atTop he).eventually_ge_atTop _
  have ev3 : ∀ᶠ x : ℝ in atTop, (60 : ℝ) ≤ x ^ (Fm.ez / 5) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have ev4 := GlobalTheory.SpecialSmall.ev_pow_le_exp he (4 * 2 ^ C) ((11 + |Fm.Ct|) * C + eps)
  have ev5 := GlobalTheory.SpecialSmall.ev_pow_le_exp he 32 (5 + eps)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (ev1.and (ev2.and (ev3.and (ev4.and ev5))))
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨h3, h16, h60, hbig, hbig2⟩ := hx0 x hx
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  exact GlobalTheory.SpecialSmall.at_one (Fm.L x i) (Fm.params x hx1 i) (Fm.sizes x hx1 i) C hC
    (by rw [hLx]; exact h3) (by rw [hLx, hLe]; exact h16) (by rw [hLx, Fm.L_ez]; exact h60)
    (by rw [hLx, hLe, hCt]; exact hbig) (by rw [hLx, hLe]; exact hbig2)
