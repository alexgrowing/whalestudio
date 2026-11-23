import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Indef.Tree

namespace OnPage

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

def nH (O : OnObj S P c) : ℝ := O.f / 2

def Xp (O : OnObj S P c) : ℝ := Real.exp (O.x ^ (O.eps / 3))

def aa (O : OnObj S P c) : ℝ := O.x * O.b

def wpp (O : OnObj S P c) : ℝ := aa O / Xp O / (O.x * nH O)

def dl2 (O : OnObj S P c) : ℝ := (O.T2 : ℝ) / nH O

def x0 (ε : ℝ) : ℝ := (2 / ε) ^ (2 / ε)

def ConstC (c : OnConst) : Prop := 1 ≤ c.C

def ConstBad (c : OnConst) : Prop := 14 ≤ c.Cb1 ∧ 66 * c.C + 4 ≤ c.Cb2

def XLarge (O : OnObj S P c) (C2 : ℝ) : Prop := 3 ≤ O.x ∧ 3 * c.C * C2 ≤ O.x ∧ x0 O.eps ≤ O.x

def ExponentSmallBound (O : OnObj S P c) : Prop := 0 < O.eps ∧ O.eps < 1 / 52

def HalfDegreeAtLeastFour (O : OnObj S P c) : Prop := 4 ≤ nH O

def PrimeCongruenceConditions (O : OnObj S P c) : Prop := O.q1.Prime ∧ O.dd.Prime ∧ O.q1 % 8 = 3 ∧ O.dd % 16 = 7

def DegreeAtLeastFortyFour (O : OnObj S P c) : Prop := 44 ≤ O.m ∧ 0 ≤ nH O

def DimensionExceedsDegreeByThree (O : OnObj S P c) : Prop := O.m + 3 ≤ O.k

def RankAndLengthLowerBounds (O : OnObj S P c) : Prop := 9 ≤ O.rr ∧ 10 ≤ O.L

def LeafSZ1 (O : OnObj S P c) : Prop := 0 ≤ O.T ∧ O.T ≤ O.b

def LeafW (O : OnObj S P c) : Prop :=
  ∃ nf : ℕ, (nf : ℝ) = O.f ∧ ∀ j, ∃ ws : Fin nf → ℝ, O.wt j = ∑ τ, ws τ ∧ ∀ τ, 0 ≤ ws τ ∧ ws τ ≤ 2 * O.b

def SupportGapBounds (O : OnObj S P c) : Prop := O.k * O.Sc ≤ wpp O ∧ Xp O * (O.Sc + O.eta) ≤ O.b

def EtaPowerBound (O : OnObj S P c) : Prop := O.eta * O.b ^ ((4 : ℝ) / 5) ≤ wpp O

def LeafSign (O : OnObj S P c) : Prop := 0 ≤ O.Sc ∧ 0 ≤ O.eta

def NodeCountBound (O : OnObj S P c) : Prop := ∃ t : ℝ, 0 ≤ t ∧ O.k + O.m * (t + 1) ≤ Xp O

def LogPrimeProductBound (O : OnObj S P c) : Prop := Real.log ((O.q1 * O.dd : ℕ) : ℝ) ≤ O.m

def ProductWithRatioBound (O : OnObj S P c) : Prop := O.k * O.bp ≤ O.b

def ConductorCongruentPrimePair (O : OnObj S P c) : Prop :=
  O.g1.Prime ∧ O.g2.Prime ∧ (O.g1 : ℝ) ≤ O.b ^ 9 ∧ (O.g2 : ℝ) ≤ O.b ^ 9 ∧ O.g1 ≠ O.g2 ∧
    ∃ M : ℕ, (O.q1 ∣ M ∧ O.dd ∣ M ∧ ∀ p ∈ O.sm, 1 < p ∧ p ∣ M) ∧ O.g1 % M = 1 ∧ O.g2 % M = 1

def SquaredTimeBound (O : OnObj S P c) : Prop := ∃ PP : ℝ, 1 ≤ PP ∧ PP ^ 3 * O.T ^ 2 ≤ O.b

def PowerTwelveBound (O : OnObj S P c) : Prop := (O.f * O.rr * O.L) ^ 12 ≤ O.b

def DiscriminantDegreeBound (O : OnObj S P c) : Prop := 0 ≤ O.DF ∧ ∃ nW : ℝ, 40 ≤ nW ∧ 2 * Real.pi * nW ≤ O.DF ^ 2

def ProductLowerBoundTwist (O : OnObj S P c) : Prop :=
  ∃ PP D : ℝ, 1 ≤ PP ∧ 1 ≤ D ∧ PP ^ 4 * D ^ 3 * O.k * O.f * O.x ≤ O.T * O.m * dl2 O

def TwistDensityBounds (O : OnObj S P c) : Prop := O.x ^ (-O.eps) ≤ dl2 O ∧ ∃ Lw : ℝ, 22 ≤ Lw ∧ dl2 O ≤ 1 / (4 * Lw)

def TimeDiscriminantBound (O : OnObj S P c) (C2 : ℝ) : Prop := O.T * O.DF ≤ 3 * C2 * O.k * O.f * O.b

def TieVd (O : OnObj S P c) : Prop :=
  0 ≤ O.vd ∧ (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 + O.vd) ≤ 11 * O.L ∧ O.q1 ∉ O.sm ∧ O.dd ∉ O.sm

def SecondRatioDefinition (O : OnObj S P c) : Prop := O.X2 = aa O / wpp O

def TieBp (O : OnObj S P c) : Prop := O.bp = aa O / Xp O

def TieNc (O : OnObj S P c) : Prop := O.Nc = dl2 O * O.k * O.b * O.x ^ (2 * O.eps) / nH O

theorem L_eq_rpow (O : OnObj S P c) : O.L = O.x ^ O.eps := by
  show Real.log (Real.exp _) = _
  exact Real.log_exp _

theorem one_le_b (O : OnObj S P c) (hx : 0 ≤ O.x) : 1 ≤ O.b :=
  Real.one_le_exp (Real.rpow_nonneg hx _)

theorem one_le_Xp (O : OnObj S P c) (hx : 0 ≤ O.x) : 1 ≤ Xp O :=
  Real.one_le_exp (Real.rpow_nonneg hx _)

theorem wt_bound (O : OnObj S P c) (hW : LeafW O) (j : Bs.J) : 0 ≤ O.wt j ∧ O.wt j ≤ 2 * O.f * O.b := by
  obtain ⟨nf, hnf, hw⟩ := hW
  obtain ⟨ws, hs, hb⟩ := hw j
  rw [hs]
  refine ⟨Finset.sum_nonneg (fun τ _ => (hb τ).1), ?_⟩
  calc ∑ τ, ws τ ≤ ∑ _τ : Fin nf, 2 * O.b := Finset.sum_le_sum (fun τ _ => (hb τ).2)
    _ = 2 * O.f * O.b := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnf]; ring

theorem Se_le_b (O : OnObj S P c) (hx : 0 ≤ O.x) (h14 : SupportGapBounds O) : O.Se ≤ O.b := by
  have h1 := one_le_Xp O hx
  have hb := one_le_b O hx
  have h2 := h14.2
  show O.Sc + O.eta ≤ O.b
  by_cases h : 0 ≤ O.Sc + O.eta
  · have : 1 * (O.Sc + O.eta) ≤ Xp O * (O.Sc + O.eta) := mul_le_mul_of_nonneg_right h1 h
    linarith
  · linarith

theorem cube_le_two_exp (y : ℝ) (hy : 0 ≤ y) : y ^ 3 ≤ 2 * Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg hy 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [sq_nonneg (y ^ 2 - 6 * y), sq_nonneg (y - 4), mul_nonneg hy (sq_nonneg (y - 4)), sq_nonneg y]

theorem le_of_sq_le_sq' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have h1 : b * b < a * a := mul_self_lt_mul_self hb hc
  nlinarith

theorem bad_b (w fSe T fkb lq f m b C1 : ℝ) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b)
    (hfk : fkb ≤ f * b) (hlq0 : 0 ≤ lq) (hlq : lq ≤ m) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC1 : 14 ≤ C1) : (2 * (w + fSe + T + 1) + 4 * fkb) * lq ≤ C1 * (f * m * b) := by
  have hfb : 0 ≤ f * b := mul_nonneg (by linarith) (by linarith)
  have hB : 2 * (w + fSe + T + 1) + 4 * fkb ≤ 10 * (f * b) + 2 * b + 2 := by linarith
  have hB0 : 0 ≤ 10 * (f * b) + 2 * b + 2 := by linarith
  have hbm0 : 0 ≤ b * m := mul_nonneg (by linarith) (by linarith)
  have h1 : b * m ≤ f * m * b := by
    calc b * m = 1 * (b * m) := by ring
      _ ≤ f * (b * m) := mul_le_mul_of_nonneg_right (by linarith) hbm0
      _ = f * m * b := by ring
  have h2 : m ≤ b * m := by
    calc m = 1 * m := by ring
      _ ≤ b * m := mul_le_mul_of_nonneg_right hb (by linarith)
  have hfmb : 0 ≤ f * m * b := by linarith
  calc (2 * (w + fSe + T + 1) + 4 * fkb) * lq ≤ (10 * (f * b) + 2 * b + 2) * lq :=
        mul_le_mul_of_nonneg_right hB hlq0
    _ ≤ (10 * (f * b) + 2 * b + 2) * m := mul_le_mul_of_nonneg_left hlq hB0
    _ = 10 * (f * m * b) + 2 * (b * m) + 2 * m := by ring
    _ ≤ 14 * (f * m * b) := by linarith
    _ ≤ C1 * (f * m * b) := mul_le_mul_of_nonneg_right hC1 hfmb

theorem bad_c (C m v w fSe T f b s L C2 : ℝ) (hC : 0 ≤ C) (hv0 : 0 ≤ v) (hs : 0 ≤ s) (hv1 : s * (2 + v) ≤ 11 * L)
    (hw0 : 0 ≤ w + fSe) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC2 : 66 * C + 4 ≤ C2) :
    s * (2 * (C * m * (2 + v) * (w + fSe)) + 2 * T + 2) ≤ C2 * (f * m * b * L) := by
  have hfb : 0 ≤ f * b := mul_nonneg (by linarith) (by linarith)
  have hm0 : 0 ≤ m := by linarith
  have hsv : 0 ≤ s * v := mul_nonneg hs hv0
  have hL : 0 ≤ L := by nlinarith
  have hs2 : 2 * s ≤ 11 * L := by nlinarith
  have hwS : w + fSe ≤ 3 * (f * b) := by linarith
  have hA : s * (2 + v) * (w + fSe) ≤ 11 * L * (3 * (f * b)) :=
    mul_le_mul hv1 hwS hw0 (by linarith)
  have hB : C * m * (s * (2 + v) * (w + fSe)) ≤ C * m * (11 * L * (3 * (f * b))) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg hC hm0)
  have hfm : 352 ≤ f * m := by nlinarith
  have hbL : 0 ≤ b * L := mul_nonneg (by linarith) hL
  have h1 : s * (2 * T + 2) ≤ s * (4 * b) := mul_le_mul_of_nonneg_left (by linarith) hs
  have h2 : 2 * s * b ≤ 11 * L * b := mul_le_mul_of_nonneg_right hs2 (by linarith)
  have h3 : 352 * (b * L) ≤ f * m * (b * L) := mul_le_mul_of_nonneg_right hfm hbL
  have hU : 0 ≤ f * m * b * L := by nlinarith
  have h4 : (66 * C + 4) * (f * m * b * L) ≤ C2 * (f * m * b * L) := mul_le_mul_of_nonneg_right hC2 hU
  nlinarith

theorem bad_d (T f r L b lg : ℝ) (hT0 : 0 ≤ T) (hT2 : T ^ 2 ≤ b) (hf : 8 ≤ f) (hr : 9 ≤ r) (hL : 10 ≤ L)
    (hZ : (f * r * L) ^ 12 ≤ b) (hlg0 : 0 ≤ lg) (hlg1 : lg ≤ 18 * L) : (4 * T + 4 * f * r ^ 2) * lg ≤ 4 * b := by
  have hb0 : 0 ≤ b := le_trans (sq_nonneg T) hT2
  have hfr : 1 ≤ f * r := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hLZ : L ≤ f * r * L := by
    calc L = 1 * L := by ring
      _ ≤ f * r * L := mul_le_mul_of_nonneg_right hfr hL0
  have hL12 : L ^ 12 ≤ b := le_trans (pow_le_pow_left₀ hL0 hLZ 12) hZ
  have hL2 : 1296 * L ^ 2 ≤ b := by
    have h10 : (10 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) hL 10
    have e : L ^ 12 = L ^ 10 * L ^ 2 := by ring
    have hL20 : 0 ≤ L ^ 2 := sq_nonneg _
    have h1296 : (1296 : ℝ) ≤ L ^ 10 := le_trans (by norm_num) h10
    have : 1296 * L ^ 2 ≤ L ^ 10 * L ^ 2 := mul_le_mul_of_nonneg_right h1296 hL20
    linarith
  have hTL : 36 * (T * L) ≤ b := by
    have hsq : (36 * (T * L)) ^ 2 ≤ b ^ 2 := by
      have e : (36 * (T * L)) ^ 2 = T ^ 2 * (1296 * L ^ 2) := by ring
      rw [e, sq b]
      exact mul_le_mul hT2 hL2 (by positivity) hb0
    exact le_of_sq_le_sq' _ _ (by positivity) hb0 hsq
  have hZ0 : 720 ≤ f * r * L := by
    have h72 : 72 ≤ f * r := by nlinarith
    nlinarith
  have hZsq : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    have e : (f * r * L) ^ 2 = (f * r ^ 2 * L) * (f * L) := by ring
    have h1' : 1 ≤ f * L := by nlinarith
    have h0' : 0 ≤ f * r ^ 2 * L := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg r)) hL0
    rw [e]
    calc f * r ^ 2 * L = (f * r ^ 2 * L) * 1 := by ring
      _ ≤ (f * r ^ 2 * L) * (f * L) := mul_le_mul_of_nonneg_left h1' h0'
  have h36 : 36 * (f * r * L) ^ 2 ≤ (f * r * L) ^ 12 := by
    have h10 : (720 : ℝ) ^ 10 ≤ (f * r * L) ^ 10 := pow_le_pow_left₀ (by norm_num) hZ0 10
    have h36' : (36 : ℝ) ≤ (f * r * L) ^ 10 := le_trans (by norm_num) h10
    have e : (f * r * L) ^ 12 = (f * r * L) ^ 10 * (f * r * L) ^ 2 := by ring
    have hz0 : 0 ≤ (f * r * L) ^ 2 := sq_nonneg _
    rw [e]
    exact mul_le_mul_of_nonneg_right h36' hz0
  have hfr2 : 36 * (f * r ^ 2 * L) ≤ b := by linarith
  have hfr20 : 0 ≤ f * r ^ 2 := mul_nonneg (by linarith) (sq_nonneg r)
  calc (4 * T + 4 * f * r ^ 2) * lg = 4 * T * lg + 4 * (f * r ^ 2) * lg := by ring
    _ ≤ 4 * T * (18 * L) + 4 * (f * r ^ 2) * (18 * L) := by
        have a1 : 4 * T * lg ≤ 4 * T * (18 * L) := mul_le_mul_of_nonneg_left hlg1 (by linarith)
        have a2 : 4 * (f * r ^ 2) * lg ≤ 4 * (f * r ^ 2) * (18 * L) :=
          mul_le_mul_of_nonneg_left hlg1 (by linarith)
        linarith
    _ = 2 * (36 * (T * L)) + 2 * (36 * (f * r ^ 2 * L)) := by ring
    _ ≤ 4 * b := by linarith

theorem leafBad_of_page (O : OnObj S P c)
    (hC : 0 ≤ c.C) (hCb1 : 14 ≤ c.Cb1) (hCb2 : 66 * c.C + 4 ≤ c.Cb2) (hx : 3 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h21 : RankAndLengthLowerBounds O) (h1 : LeafSZ1 O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h121 : LogPrimeProductBound O) (h1232 : ProductWithRatioBound O) (h75 : ConductorCongruentPrimePair O) (h19 : SquaredTimeBound O) (h18 : PowerTwelveBound O)
    (tVd : TieVd O) : LeafBad O := by
  have hx0 : 0 ≤ O.x := by linarith
  have hb := one_le_b O hx0
  have hf : 8 ≤ O.f := by
    have h4 : 4 ≤ O.f / 2 := hN4
    linarith
  have hm : 44 ≤ O.m := h1246.1
  have hSe := Se_le_b O hx0 h14
  have hfS : O.f * O.Se ≤ O.f * O.b := mul_le_mul_of_nonneg_left hSe (by linarith)
  refine ⟨show 0 ≤ c.Cb1 by linarith, show 0 ≤ c.Cb2 by linarith, fun j => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨_, hw1⟩ := wt_bound O hW j
    have hfk : O.f * O.k * O.bp ≤ O.f * O.b := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1232 (by linarith)
    exact bad_b (O.wt j) (O.f * O.Se) O.T (O.f * O.k * O.bp) (Real.log ((O.q1 * O.dd : ℕ) : ℝ)) O.f O.m O.b
      c.Cb1 hw1 hfS h1.2 hfk (Real.log_natCast_nonneg _) h121 hf hm hb hCb1
  · obtain ⟨hw0, hw1⟩ := wt_bound O hW j
    by_cases hS0 : 0 ≤ O.wt j + O.f * O.Se
    · exact bad_c c.C O.m O.vd (O.wt j) (O.f * O.Se) O.T O.f O.b _ O.L c.Cb2 hC tVd.1
        (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p) tVd.2.1 hS0 hw1 hfS h1.2 hf hm hb hCb2
    · have h0 := bad_c c.C O.m O.vd 0 0 O.T O.f O.b _ O.L c.Cb2 hC tVd.1
        (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p) tVd.2.1 (by norm_num) (by nlinarith) (by nlinarith) h1.2 hf hm hb hCb2
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p)) h0
      have hcm : 0 ≤ c.C * O.m * (2 + O.vd) := mul_nonneg (mul_nonneg hC (by linarith)) (by linarith [tVd.1])
      have := mul_nonpos_of_nonneg_of_nonpos hcm (le_of_lt (not_le.1 hS0))
      show 2 * (c.C * O.m * (2 + O.vd) * (O.wt j + O.f * O.Se)) + 2 * O.T + 2 ≤ _
      linarith
  · obtain ⟨hp1, hp2, hg1, hg2, -⟩ := h75
    obtain ⟨PP, hPP, hPPT⟩ := h19
    have hlogb : Real.log O.b = O.L := rfl
    have hg1p : (0 : ℝ) < (O.g1 : ℝ) := by exact_mod_cast hp1.pos
    have hg2p : (0 : ℝ) < (O.g2 : ℝ) := by exact_mod_cast hp2.pos
    have hlg1 : Real.log (O.g1 : ℝ) ≤ 9 * O.L := by
      calc Real.log (O.g1 : ℝ) ≤ Real.log (O.b ^ 9) := Real.log_le_log hg1p hg1
        _ = 9 * O.L := by rw [Real.log_pow, hlogb]; norm_num
    have hlg2 : Real.log (O.g2 : ℝ) ≤ 9 * O.L := by
      calc Real.log (O.g2 : ℝ) ≤ Real.log (O.b ^ 9) := Real.log_le_log hg2p hg2
        _ = 9 * O.L := by rw [Real.log_pow, hlogb]; norm_num
    have hlg : Real.log ((O.g1 * O.g2 : ℕ) : ℝ) = Real.log (O.g1 : ℝ) + Real.log (O.g2 : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hg1p.ne' hg2p.ne']
    have hl1 : 0 ≤ Real.log (O.g1 : ℝ) := Real.log_natCast_nonneg _
    have hl2 : 0 ≤ Real.log (O.g2 : ℝ) := Real.log_natCast_nonneg _
    have hT2 : O.T ^ 2 ≤ O.b := by
      have h3 : 1 ≤ PP ^ 3 := one_le_pow₀ hPP
      have : 1 * O.T ^ 2 ≤ PP ^ 3 * O.T ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      linarith
    exact bad_d O.T O.f O.rr O.L O.b _ h1.1 hT2 hf h21.1 h21.2 h18 (by rw [hlg]; linarith)
      (by rw [hlg]; linarith)

theorem dfx_bound (DF x k f m b T de2 PP D C2 : ℝ) (hDF0 : 0 ≤ DF) (hPP : 1 ≤ PP) (hD : 1 ≤ D)
    (hT : PP ^ 4 * D ^ 3 * k * f * x ≤ T * m * de2) (hde0 : 0 ≤ de2) (hde1 : de2 ≤ 1)
    (hZ3 : T * DF ≤ 3 * C2 * k * f * b) (hC2 : 0 ≤ C2) (hk : 0 < k) (hf : 0 < f) (hx0 : 0 ≤ x)
    (hm0 : 0 ≤ m) (hb0 : 0 ≤ b) : DF * x ≤ 3 * C2 * m * b := by
  have hQ : 1 ≤ PP ^ 4 * D ^ 3 := by
    have h1' : 1 ≤ PP ^ 4 := one_le_pow₀ hPP
    have h2' : 1 ≤ D ^ 3 := one_le_pow₀ hD
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ PP ^ 4 * D ^ 3 := mul_le_mul h1' h2' (by norm_num) (by linarith)
  have hkfx : 0 ≤ k * f * x := mul_nonneg (mul_nonneg hk.le hf.le) hx0
  have e1 : DF * (k * f * x) ≤ DF * (PP ^ 4 * D ^ 3 * k * f * x) := by
    apply mul_le_mul_of_nonneg_left _ hDF0
    calc k * f * x = 1 * (k * f * x) := by ring
      _ ≤ (PP ^ 4 * D ^ 3) * (k * f * x) := mul_le_mul_of_nonneg_right hQ hkfx
      _ = PP ^ 4 * D ^ 3 * k * f * x := by ring
  have e2 : DF * (PP ^ 4 * D ^ 3 * k * f * x) ≤ DF * (T * m * de2) := mul_le_mul_of_nonneg_left hT hDF0
  have e4 : (T * DF) * (m * de2) ≤ (3 * C2 * k * f * b) * (m * de2) :=
    mul_le_mul_of_nonneg_right hZ3 (mul_nonneg hm0 hde0)
  have hK0 : 0 ≤ 3 * C2 * k * f * b := by positivity
  have hmd : m * de2 ≤ m := by
    calc m * de2 ≤ m * 1 := mul_le_mul_of_nonneg_left hde1 hm0
      _ = m := by ring
  have e5 : (3 * C2 * k * f * b) * (m * de2) ≤ (3 * C2 * k * f * b) * m := mul_le_mul_of_nonneg_left hmd hK0
  have hkf : 0 < k * f := mul_pos hk hf
  have e6 : (k * f) * (DF * x) ≤ (k * f) * (3 * C2 * m * b) := by
    have a : (k * f) * (DF * x) = DF * (k * f * x) := by ring
    have a' : DF * (T * m * de2) = (T * DF) * (m * de2) := by ring
    have a'' : (k * f) * (3 * C2 * m * b) = (3 * C2 * k * f * b) * m := by ring
    rw [a, a'']
    rw [a'] at e2
    linarith
  exact le_of_mul_le_mul_left e6 hkf

theorem two_cube_le (y n : ℝ) (hy : 0 ≤ y) (hn : 4 ≤ n) : 2 * y ^ 3 ≤ Real.exp y * n := by
  have h := cube_le_two_exp y hy
  have he : 0 < Real.exp y := Real.exp_pos y
  have : Real.exp y * 4 ≤ Real.exp y * n := mul_le_mul_of_nonneg_left hn he.le
  linarith

set_option maxHeartbeats 1000000 in

theorem leafSizes_of_page (O : OnObj S P c) (C2 : ℝ) (hC2 : 0 ≤ C2) (hC : 1 ≤ c.C)
    (hx : 3 ≤ O.x) (hxC : 3 * c.C * C2 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h21 : RankAndLengthLowerBounds O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h011 : EtaPowerBound O) (hSg : LeafSign O) (h1243 : NodeCountBound O) (h13 : DiscriminantDegreeBound O)
    (h231 : ProductLowerBoundTwist O) (h44 : TwistDensityBounds O) (tX2 : SecondRatioDefinition O) (tZ3 : TimeDiscriminantBound O C2) : LeafSizes O := by
  have hx0 : 0 ≤ O.x := by linarith
  have hxp : 0 < O.x := by linarith
  have hb := one_le_b O hx0
  have hbpos : 0 < O.b := by linarith
  have hXp := one_le_Xp O hx0
  have hn4 : 4 ≤ nH O := hN4
  have hf : 8 ≤ O.f := by
    have h4 : 4 ≤ O.f / 2 := hN4
    linarith
  have hm : 44 ≤ O.m := h1246.1
  have hk : O.m + 3 ≤ O.k := h29
  have hL : 10 ≤ O.L := h21.2
  have hLx : O.L = O.x ^ O.eps := L_eq_rpow O
  have he0 : 0 < O.eps := hEps.1
  have hkX : O.k ≤ Xp O := by
    obtain ⟨t, ht, hN⟩ := h1243
    have : 0 ≤ O.m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hkpos : 0 < O.k := by linarith
  have hlogk : Real.log O.k ≤ O.L := by
    calc Real.log O.k ≤ Real.log (Xp O) := Real.log_le_log hkpos hkX
      _ = O.x ^ (O.eps / 3) := Real.log_exp _
      _ ≤ O.x ^ O.eps := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = O.L := hLx.symm
  obtain ⟨hDF0, nW, hnW, hDF2⟩ := h13
  have hDF1 : 1 < O.DF := by
    have hpi := Real.pi_gt_three
    have h80 : 1 < O.DF ^ 2 := by nlinarith
    by_contra hc
    push_neg at hc
    have : O.DF ^ 2 ≤ 1 := by nlinarith
    linarith
  have hY1 : 1 < O.Y := by
    show 1 < c.C * O.DF
    nlinarith
  obtain ⟨PP, D, hPP, hD, hT⟩ := h231
  obtain ⟨hde0', Lw, hLw, hde1'⟩ := h44
  have hde0 : 0 ≤ dl2 O := le_trans (Real.rpow_nonneg hx0 _) hde0'
  have hde1 : dl2 O ≤ 1 := by
    have : 1 / (4 * Lw) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hDFx := dfx_bound O.DF O.x O.k O.f O.m O.b O.T (dl2 O) PP D C2 hDF0 hPP hD hT hde0 hde1 tZ3 hC2 hkpos
    (by linarith) hx0 (by linarith) hbpos.le
  have hYmb : O.Y ≤ O.m * O.b := by
    show c.C * O.DF ≤ O.m * O.b
    have h1' : (c.C * O.DF) * O.x ≤ c.C * (3 * C2 * O.m * O.b) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDFx (by linarith)
    have hmb : 0 ≤ O.m * O.b := mul_nonneg (by linarith) hbpos.le
    have h2' : c.C * (3 * C2 * O.m * O.b) ≤ (O.m * O.b) * O.x := by
      calc c.C * (3 * C2 * O.m * O.b) = (3 * c.C * C2) * (O.m * O.b) := by ring
        _ ≤ O.x * (O.m * O.b) := mul_le_mul_of_nonneg_right hxC hmb
        _ = (O.m * O.b) * O.x := by ring
    exact le_of_mul_le_mul_right (le_trans h1' h2') hxp
  have hlogY : Real.log O.Y ≤ 2 * O.L := by
    have hY0 : 0 < O.Y := by linarith
    have hmp : 0 < O.m := by linarith
    have hlm : Real.log O.m ≤ Real.log O.k := Real.log_le_log hmp (by linarith)
    calc Real.log O.Y ≤ Real.log (O.m * O.b) := Real.log_le_log hY0 hYmb
      _ = Real.log O.m + O.L := by rw [Real.log_mul hmp.ne' hbpos.ne']; rfl
      _ ≤ 2 * O.L := by linarith
  have hy : O.x ^ O.eps = (O.x ^ (O.eps / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy0 : 0 ≤ O.x ^ (O.eps / 3) := Real.rpow_nonneg hx0 _
  have hy3 : O.L = (O.x ^ (O.eps / 3)) ^ 3 := by rw [hLx, hy]
  have hy2 : 2 ≤ O.x ^ (O.eps / 3) := by
    by_contra hc
    push_neg at hc
    have : (O.x ^ (O.eps / 3)) ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ hc hy0 (by norm_num)
    linarith
  have hkb : O.k ≤ O.b ^ ((4 : ℝ) / 5) := by
    have hb45 : O.b ^ ((4 : ℝ) / 5) = Real.exp ((O.x ^ (O.eps / 3)) ^ 3 * (4 / 5)) := by
      show (Real.exp (O.x ^ O.eps)) ^ ((4 : ℝ) / 5) = _
      rw [← Real.exp_mul, hy]
    rw [hb45]
    have hyy : O.x ^ (O.eps / 3) ≤ (O.x ^ (O.eps / 3)) ^ 3 * (4 / 5) := by
      have h4 : (0 : ℝ) ≤ (O.x ^ (O.eps / 3)) ^ 2 * (4 / 5) - 1 := by nlinarith
      nlinarith [mul_nonneg hy0 h4]
    calc O.k ≤ Xp O := hkX
      _ = Real.exp (O.x ^ (O.eps / 3)) := rfl
      _ ≤ Real.exp ((O.x ^ (O.eps / 3)) ^ 3 * (4 / 5)) := Real.exp_le_exp.mpr hyy
  have hXn : 0 < Xp O * nH O := mul_pos (by linarith) (by linarith)
  have hwpp : wpp O = O.b / (Xp O * nH O) := by
    unfold wpp aa
    have : O.x ≠ 0 := hxp.ne'
    have : Xp O ≠ 0 := by linarith
    have : nH O ≠ 0 := by linarith
    field_simp
  have hkS : O.k * O.Se ≤ 2 * wpp O := by
    have a1 : O.k * O.Sc ≤ wpp O := h14.1
    have a2 : O.k * O.eta ≤ wpp O := by
      have h' : O.eta * O.b ^ ((4 : ℝ) / 5) ≤ wpp O := h011
      have : O.k * O.eta ≤ O.b ^ ((4 : ℝ) / 5) * O.eta := mul_le_mul_of_nonneg_right hkb hSg.2
      linarith
    show O.k * (O.Sc + O.eta) ≤ _
    linarith
  have hexp : 2 * O.L ≤ Xp O * nH O := by
    rw [hy3]
    exact two_cube_le _ _ hy0 hn4
  have hkSL : O.k * O.Se * O.L ≤ O.m * O.b := by
    have hL0 : 0 ≤ O.L := by linarith
    calc O.k * O.Se * O.L ≤ 2 * wpp O * O.L := mul_le_mul_of_nonneg_right hkS hL0
      _ = O.b * (2 * O.L) / (Xp O * nH O) := by rw [hwpp]; ring
      _ ≤ O.b * (Xp O * nH O) / (Xp O * nH O) := by
          apply div_le_div_of_nonneg_right _ hXn.le
          exact mul_le_mul_of_nonneg_left hexp hbpos.le
      _ = O.b := by field_simp
      _ = 1 * O.b := by ring
      _ ≤ O.m * O.b := mul_le_mul_of_nonneg_right (by linarith) hbpos.le
  have hX2 : O.k ≤ O.X2 := by
    rw [tX2, hwpp]
    unfold aa
    have e : O.x * O.b / (O.b / (Xp O * nH O)) = (O.x * nH O) * Xp O := by
      field_simp
    rw [e]
    have hxn : 1 ≤ O.x * nH O := by nlinarith
    calc O.k ≤ Xp O := hkX
      _ = 1 * Xp O := by ring
      _ ≤ (O.x * nH O) * Xp O := mul_le_mul_of_nonneg_right hxn (le_trans zero_le_one hXp)
  exact ⟨fun j => wt_bound O hW j, hY1, hlogY, hYmb, hkSL, hX2, hlogk, le_trans (by norm_num : (1 : ℝ) ≤ 10) hL⟩

theorem ne_of_mod_dvd {g a M : ℕ} (h : g % M = 1) (ha : a ∣ M) (ha1 : 1 < a) : a ≠ g := by
  intro hag
  rw [hag] at ha ha1
  have h2 := Nat.mod_mod_of_dvd g ha
  rw [h, Nat.mod_self, Nat.mod_eq_of_lt ha1] at h2
  exact absurd h2 (by norm_num)

theorem leafPage_of (O : OnObj S P c) (hC : ConstC c) (hx : 3 ≤ O.x) (hN4 : HalfDegreeAtLeastFour O) (h12 : PrimeCongruenceConditions O)
    (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h1 : LeafSZ1 O) (hSg : LeafSign O) (h75 : ConductorCongruentPrimePair O)
    (tVd : TieVd O) (tBp : TieBp O) (tNc : TieNc O) : LeafPage O := by
  obtain ⟨hq, hd, hq8, hd16⟩ := h12
  obtain ⟨hg1, hg2, -, -, hne, n, ⟨dq, dd', hsm⟩, hm1, hm2⟩ := h75
  have hx0 : 0 ≤ O.x := by linarith
  have hb : 1 ≤ O.b := one_le_b O hx0
  have hn4 : 4 ≤ nH O := hN4
  have hnp : 0 < nH O := by linarith
  have hf : 8 ≤ O.f := by have : nH O = O.f / 2 := rfl; linarith
  have hm : 44 ≤ O.m := h1246.1
  have hk : O.m + 3 ≤ O.k := h29
  have hbp : 0 ≤ O.bp := by
    rw [tBp]; unfold aa Xp
    exact div_nonneg (mul_nonneg hx0 (by linarith)) (Real.exp_pos _).le
  have hvd : 0 ≤ O.vd := tVd.1
  have hNc : 0 ≤ O.Nc := by
    rw [tNc]; unfold dl2
    have : 0 ≤ (O.T2 : ℝ) / nH O := div_nonneg (Nat.cast_nonneg _) hnp.le
    have : 0 ≤ O.x ^ (2 * O.eps) := Real.rpow_nonneg hx0 _
    have : 0 ≤ (O.T2 : ℝ) / nH O * O.k * O.b := by
      apply mul_nonneg (mul_nonneg (by assumption) (by linarith)) (by linarith)
    exact div_nonneg (mul_nonneg (by assumption) (by assumption)) hnp.le
  refine ⟨hC, by linarith, by linarith, hf, h1.1, hSg.1, hSg.2, hbp, hvd, hNc, hg1, hg2, hq, hd, hne, by omega,
    ne_of_mod_dvd hm1 dq hq.one_lt, ne_of_mod_dvd hm2 dq hq.one_lt, ne_of_mod_dvd hm1 dd' hd.one_lt,
    ne_of_mod_dvd hm2 dd' hd.one_lt, fun h => ne_of_mod_dvd hm1 (hsm _ h).2 (hsm _ h).1 rfl,
    fun h => ne_of_mod_dvd hm2 (hsm _ h).2 (hsm _ h).1 rfl, tVd.2.2.1, tVd.2.2.2, by linarith⟩

def PageLeaves (O : OnObj S P c) (C2 : ℝ) : Prop :=
  ExponentSmallBound O ∧ HalfDegreeAtLeastFour O ∧ PrimeCongruenceConditions O ∧ DegreeAtLeastFortyFour O ∧ DimensionExceedsDegreeByThree O ∧ RankAndLengthLowerBounds O ∧ LeafSZ1 O ∧ LeafW O ∧ SupportGapBounds O ∧
    EtaPowerBound O ∧ LeafSign O ∧ NodeCountBound O ∧ LogPrimeProductBound O ∧ ProductWithRatioBound O ∧ ConductorCongruentPrimePair O ∧ SquaredTimeBound O ∧ PowerTwelveBound O ∧
    DiscriminantDegreeBound O ∧ ProductLowerBoundTwist O ∧ TwistDensityBounds O ∧ TimeDiscriminantBound O C2 ∧ TieVd O ∧ SecondRatioDefinition O ∧ TieBp O ∧ TieNc O

abbrev pageC : OnConst := ⟨1, 14, 70⟩

def px : ℝ := (10 : ℝ) ^ (1200 : ℕ)

def pe : ℝ := 1 / 100

variable (K)

abbrev pageO (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) : OnObj (exampleIndefiniteData K v0 Tw0 0) Unit pageC where
  nZ := fun _ => 1
  ρ := fun _ => 1
  U := ⊤
  ψ := fun _ => 1
  V₀ := fun _ => ⊤
  e := fun _ => LinearMap.id
  Ms := fun _ => stdLat K 1
  φ := fun _ => LinearMap.id
  Th1 := fun _ _ => stdLat K 1
  Th := fun _ _ => stdLat K 1
  ThK := fun _ _ => stdLat K 1
  Th0 := fun _ _ => stdLat K 1
  ThJ := fun _ _ => stdLat K 1
  X₃ := fun _ _ => stdLat K 1
  σ := fun _ _ => 1
  a := fun _ _ => 1
  E := fun _ _ => 0
  r1 := fun _ _ => 0
  r2 := fun _ _ => 0
  pde := 0
  ε0 := fun _ _ => 0
  nX := fun _ _ => 1
  θ' := fun _ _ => LinearMap.id
  eX := fun _ _ => LinearMap.id
  pr := fun _ _ => LinearMap.id
  Mt := fun _ _ => stdLat K 1
  nnK := fun _ => 1
  Jp := fun _ _ => 0
  k := 47
  m := 44
  f := 256
  bp := px * Real.exp (px ^ pe) / Real.exp (px ^ (pe / 3))
  Sc := 0
  eta := 0
  T := px * 100000
  DF := 16
  X2 := px * Real.exp (px ^ pe) / (px * Real.exp (px ^ pe) / Real.exp (px ^ (pe / 3)) / (px * (256 / 2)))
  x := px
  eps := pe
  vd := 8
  rr := 90
  de2 := 1
  Nc := ((1 : ℕ) : ℝ) / (256 / 2) * 47 * Real.exp (px ^ pe) * px ^ (2 * pe) / (256 / 2)
  wt := fun _ => 0
  th := fun _ => 0
  ad := fun _ => 0
  T2 := 1
  g1 := 118273
  g2 := 275969
  q1 := 11
  dd := 7
  sm := {2}

variable {K}

variable (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))

end OnPage

end Formalism.L2.Indef.Tree
