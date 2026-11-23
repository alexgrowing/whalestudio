import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.DimensionConstantBounds

noncomputable section

namespace GlobalTheory.ConstCompare

open Formalism.BasicNotions Formalism.MainNotions NumberField
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

theorem choose_two_add (p q : ℕ) :
    p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ← ih]
    simp only [Nat.choose_one_right]
    ring

theorem dimY_eq (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WeightFamilies.dimY D j = DimensionConstantBounds.dimFlag D := by
  unfold WeightFamilies.dimY DimensionConstantBounds.dimFlag
  rw [choose_two_add]
  have h3 := D.R.m_add_three_le_k
  have : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    unfold Ranks.sigW Ranks.r; dsimp only; omega
  rw [this]

theorem q_eq (D : D7) : WeightAlgebra.qq D = DimensionConstantBounds.q D := rfl

theorem g0_eq (D : D7) : WeightAlgebra.g0 D = DimensionConstantBounds.g0 D := rfl

theorem degF_eq {j : ℕ} (w : WeightFamilies.Wt D j) : WeightAlgebra.DF w = DimensionConstantBounds.degF w := rfl

theorem c_eq_cOf (L : SizeData₂ D) {j : ℕ} (C A : ℝ) (w : WeightFamilies.Wt D j) :
    WeightAlgebra.cc D L C A 7 w = DimensionConstantBounds.cOf D (WeightFamilies.PPv D L C A) (DimensionConstantBounds.degF w) := by
  unfold WeightAlgebra.cc DimensionConstantBounds.cOf; rw [DimensionConstantBounds.RR_eq]; rfl

theorem c_eq (L : SizeData₂ D) {j : ℕ} (CP : ℝ) (w : WeightFamilies.Wt D j) :
    WeightAlgebra.cc D L CP 12 7 w = DimensionConstantBounds.c L CP (DimensionConstantBounds.degF w) := by
  rw [c_eq_cOf]; unfold DimensionConstantBounds.c; rw [DimensionConstantBounds.PP_eq_PPv]

theorem lamStar_eq (D : D7) : WeightAlgebra.lamStar D = DimensionConstantBounds.LamStar D := rfl

theorem PN_eq (L : SizeData₂ D) : WeightAlgebra.PN D L = DimensionConstantBounds.PN L := rfl

theorem normShift_eq (D : D7) (j : ℕ) : WeightAlgebra.n0 D j = DimensionConstantBounds.n0 D j := rfl

theorem Z_eq (L : SizeData₂ D) : WeightAlgebra.Zb D L = DimensionConstantBounds.Z L := rfl

theorem lrd_eq (D : D7) : WeightAlgebra.lrd D = DimensionConstantBounds.lrd D := by
  rw [DimensionConstantBounds.lrd_eq]; rfl

theorem PU_eq (D : D7) : WeightAlgebra.PU D = DimensionConstantBounds.PU D := by
  unfold WeightAlgebra.PU DimensionConstantBounds.PU DimensionConstantBounds.PUn; rw [lrd_eq]

theorem PO_eq (L : SizeData₂ D) : WeightAlgebra.PO D L = DimensionConstantBounds.PO L := rfl

theorem flipOneTwo_eq_sizeConstantAtWeight (D : D7) (nW : ℕ) : WeightAlgebra.sizeConstantAtParamsWeight D nW = DimensionConstantBounds.sizeConstantAtWeight D nW := by
  have h : (WeightAlgebra.g0 D : ℝ) = 2 * (DimensionConstantBounds.r1 : ℝ) ^ 4 * (D.R.r : ℝ) := by
    unfold WeightAlgebra.g0 DimensionConstantBounds.r1; push_cast; ring
  unfold WeightAlgebra.sizeConstantAtParamsWeight DimensionConstantBounds.sizeConstantAtWeight; rw [h]

theorem weight_constant_eq_dimension_constant (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WeightAlgebra.DivisibilityWeightConstant D j = DimensionConstantBounds.DivisibilityWeightConstant D := by
  unfold WeightAlgebra.DivisibilityWeightConstant DimensionConstantBounds.DivisibilityWeightConstant DimensionConstantBounds.r1; rw [dimY_eq D h1 h2]; push_cast; rfl

theorem weightAlgebra_PI4_eq_dimensionConstant_PI4 (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (PLam lNc : ℝ) :
    WeightAlgebra.PI4 D j PLam lNc = DimensionConstantBounds.PI4 D PLam lNc := by
  unfold WeightAlgebra.PI4 DimensionConstantBounds.PI4; rw [dimY_eq D h1 h2]; rfl

theorem log_rd (K : Type) [Field K] [NumberField K] :
    Real.log (|((discr K : ℤ) : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))) =
      Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K := by
  have h : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  rw [Real.log_rpow h]; ring

theorem G_eq (L : SizeData₂ D) (X : WeightFamilies.Prov D) (PLam : ℝ) (po : ℕ) :
    WeightAlgebra.Gc L X PLam po = DimensionConstantBounds.G L X PLam po := by
  unfold WeightAlgebra.Gc DimensionConstantBounds.G DimensionConstantBounds.GOf DimensionConstantBounds.fieldSize DimensionConstantBounds.LamPlus
  rw [log_rd, log_rd]; rfl

theorem ring_iff (L : SizeData₂ D) (X : WeightFamilies.Prov D) : WeightAlgebra.OPO L X ↔ DimensionConstantBounds.RingBound L X := by
  unfold WeightAlgebra.OPO DimensionConstantBounds.RingBound WeightFamilies.rdO WeightFamilies.degO
  rw [log_rd]; rfl

theorem log_bad_le_lamStar (D : D7) :
    Real.log (D.host.QS * (D.host.q : ℝ) * D.host.d * D.host.g 0 * D.host.g 1) ≤ WeightAlgebra.lamStar D := by
  have hq : (0 : ℝ) < D.host.q := by exact_mod_cast D.host.hyp.1.pos
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have h0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have h1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hn : (1 : ℝ) ≤ D.R.n := by
    exact_mod_cast D.R.ord_pos
  unfold WeightAlgebra.lamStar
  rw [DimensionConstantBounds.half_f, ← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by have := D.host.QS_pos; positivity) ?_
  have hQ : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
  have h2 : (D.host.QS : ℝ) ≤ 4 * (D.R.n : ℝ) ^ 2 := by
    have : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    nlinarith
  have h3 : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d * D.host.g 0 * D.host.g 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem domAt_iff (L : SizeData₂ D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (nW : ℕ) (CP : ℝ) :
    WeightAlgebra.DomAt D L j nW CP ↔
      (10 ^ 3 ≤ CP ∧ (1 * CP) ^ 20 ≤ DimensionConstantBounds.Z L ∧
        DimensionConstantBounds.PU D ≤ DimensionConstantBounds.grade L CP 1 ∧ DimensionConstantBounds.LamStar D ≤ DimensionConstantBounds.grade L CP 1 ∧
        DimensionConstantBounds.PN L ≤ DimensionConstantBounds.grade L CP 1 ∧ DimensionConstantBounds.PO L ≤ DimensionConstantBounds.grade L CP 2 ∧
        (DimensionConstantBounds.n0 D j : ℝ) ≤ DimensionConstantBounds.grade L CP 3 ∧ DimensionConstantBounds.sizeConstantAtWeight D nW ≤ DimensionConstantBounds.grade L CP 4 ∧
        DimensionConstantBounds.DivisibilityWeightConstant D ≤ DimensionConstantBounds.grade L CP 10) := by
  unfold WeightAlgebra.DomAt DimensionConstantBounds.grade
  rw [PU_eq, flipOneTwo_eq_sizeConstantAtWeight, weight_constant_eq_dimension_constant D h1 h2, PN_eq, PO_eq, normShift_eq, Z_eq, pow_one, one_mul,
    show (10 : ℝ) ^ 3 = 1000 by norm_num]
  have hb := log_bad_le_lamStar D
  have hN : (D.host.condN : ℝ) = D.host.QS * (D.host.q : ℝ) * D.host.d := by
    rw [show D.host.condN = D.host.QS * D.host.q * D.host.d from rfl]; push_cast; ring
  rw [← hN] at hb
  rw [lamStar_eq] at hb ⊢
  constructor
  · rintro ⟨a, b, c, d, -, e, f, g, h, i⟩
    exact ⟨a, b, e, c, d, f, g, h, i⟩
  · rintro ⟨a, b, e, c, d, f, g, h, i⟩
    exact ⟨a, b, c, d, hb.trans c, e, f, g, h, i⟩

theorem dom_iff {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (CP : ℝ) :
    (∀ j, 1 ≤ j → j ≤ D.R.m → WeightAlgebra.DomAt D L j T.nWn CP) ↔ DimensionConstantBounds.Dom T CP := by
  unfold DimensionConstantBounds.Dom DimensionConstantBounds.DomWith DimensionConstantBounds.sizeConstantAtParamsWeight
  constructor
  · intro H
    have hm := D.R.two_le_m
    obtain ⟨a, b, c, d, e, f, -, h, i⟩ := (domAt_iff L le_rfl (by omega) _ _).1 (H 1 le_rfl (by omega))
    exact ⟨a, b, c, d, e, f, fun j h1 h2 => ((domAt_iff L h1 h2 _ _).1 (H j h1 h2)).2.2.2.2.2.2.1, h, i⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i⟩ j h1 h2
    exact (domAt_iff L h1 h2 _ _).2 ⟨a, b, c, d, e, f, g j h1 h2, h, i⟩

theorem six_le_r (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  unfold Ranks.r; omega

def RowsFirst (L : SizeData₂ D) (C : ℝ) : Prop :=
  (D.R.f : ℝ) * D.R.r ≤ L.sc.x ^ C ∧ |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps

def RowsSecond (L : SizeData₂ D) : Prop :=
  L.sc.x ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ∧
  logdE D / (2 * (D.R.f : ℝ)) + |L.logDerivativeAtOne| ≤ 2 * L.sc.L ∧
  (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ D.host.rdE ^ 3

theorem rdE_nonneg (D : D7) : 0 ≤ D.host.rdE := by
  unfold Host.rdE; positivity

theorem x_le_of_sq_le_f_mul_r (L : SizeData₂ D) (h : L.sc.x ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ)) : L.sc.x ≤ (D.R.f : ℝ) * D.R.r := by
  have := L.sc.one_lt_alt
  nlinarith

theorem row_rd (D : D7) (h : (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ D.host.rdE ^ 3) :
    2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := by
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast DimensionConstantBounds.f_pos D
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have h1 : (1 : ℝ) ≤ 2 * (D.R.f : ℝ) * D.R.m := by nlinarith
  have h2 : (2 * (D.R.f : ℝ) * D.R.m) ^ 3 ≤ D.host.rdE ^ 3 :=
    (pow_le_pow_right₀ h1 (by norm_num)).trans h
  exact le_of_pow_le_pow_left₀ (by norm_num) (rdE_nonneg D) h2

theorem log_abs_discr_le (L : SizeData₂ D) {C : ℝ} (hC : 1 ≤ C)
    (h : logdE D / (2 * (D.R.f : ℝ)) + |L.logDerivativeAtOne| ≤ 2 * L.sc.L) :
    Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ C * ((D.R.f : ℝ) * D.R.r * L.sc.L) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast DimensionConstantBounds.f_pos D
  have hr : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have h4 : logdE D / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by linarith [abs_nonneg L.logDerivativeAtOne]
  rw [div_le_iff₀ (by positivity)] at h4
  have h5 : 0 < (D.R.f : ℝ) * L.sc.L := by positivity
  have h6 : (4 : ℝ) ≤ C * D.R.r := by nlinarith
  change logdE D ≤ _
  nlinarith [mul_le_mul_of_nonneg_right h6 h5.le]

theorem sizes_iff (L : SizeData₂ D) (C : ℝ) :
    (WeightAlgebra.ParA L C ∧ RowsSecond L) ↔ (DimensionConstantBounds.Sizes L C ∧ RowsFirst L C) := by
  constructor
  · rintro ⟨⟨-, a2, -, a4, a5, a6, a7, a8, a9, -⟩, b1, b2, b3⟩
    exact ⟨⟨b1, b2, a4, a5, a7, ⟨a8, a9⟩, b3⟩, a2, a6⟩
  · rintro ⟨⟨b1, b2, a4, a5, a7, ⟨a8, a9⟩, b3⟩, a2, a6⟩
    have hC : 1 ≤ C := by
      have h := (x_le_of_sq_le_f_mul_r L b1).trans a2
      rw [← Real.rpow_le_rpow_left_iff L.sc.one_lt_alt, Real.rpow_one]; exact h
    exact ⟨⟨x_le_of_sq_le_f_mul_r L b1, a2, log_abs_discr_le L hC b2, a4, a5, a6, a7, a8, a9, row_rd D b3⟩, b1, b2, b3⟩

theorem fr_le (L : SizeData₂ D) {C : ℝ} (hC : 2 * L.Ct ≤ C) : (D.R.f : ℝ) * D.R.r ≤ L.sc.x ^ C := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have h1 := D.R.rank_add_five_le
  have h2 := D.R.f_le_k
  have h3 := D.R.two_le_m
  have hr : (D.R.r : ℝ) ≤ D.R.t := by
    have : D.R.r ≤ D.R.t := by unfold Ranks.r; omega
    exact_mod_cast this
  have hf : (D.R.f : ℝ) ≤ D.R.t := by
    have : D.R.f ≤ D.R.t := by unfold Ranks.f Ranks.n; omega
    exact_mod_cast this
  have ht := L.t_win.2
  calc (D.R.f : ℝ) * D.R.r ≤ L.sc.x ^ L.Ct * L.sc.x ^ L.Ct :=
        mul_le_mul (hf.trans ht) (hr.trans ht) (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _)
    _ = L.sc.x ^ (2 * L.Ct) := by rw [← Real.rpow_add hx]; congr 1; ring
    _ ≤ L.sc.x ^ C := Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le hC

theorem parA_of_sizes (L : SizeData₂ D) {C CA : ℝ} (h : DimensionConstantBounds.Sizes L C) (hL : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps)
    (h1 : C ≤ CA) (h2 : 2 * L.Ct ≤ CA) : WeightAlgebra.ParA L CA := by
  have hL0 : 0 < L.sc.L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  obtain ⟨b1, b2, a4, a5, a7, a8, b3⟩ := h
  exact ((sizes_iff L CA).2 ⟨⟨b1, b2, a4, a5, a7.trans (mul_le_mul_of_nonneg_right h1 hL0.le), a8, b3⟩,
    fr_le L h2, hL⟩).1

theorem sizes_bounds_of_sizesAt (L : SizeData₂ D) (h : SizesAt L) :
    L.sc.x ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ∧
      logdE D / (2 * (D.R.f : ℝ)) + |L.logDerivativeAtOne| ≤ 2 * L.sc.L ∧ |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hn : (1 : ℝ) ≤ D.R.n := by
    exact_mod_cast D.R.ord_pos
  have hr : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hL' : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps := hQ.2.2.2.2.2.1
  refine ⟨?_, ?_, hL'⟩
  · have h1 : L.sc.x ^ (2 : ℝ) ≤ D.R.n :=
      (Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)).trans hN.1
    rw [Real.rpow_two] at h1
    rw [hf]; nlinarith
  · rw [← DimensionConstantBounds.lrd_eq]
    have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.pos
    have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h1 : D.host.rdE ≤ szCond L := by
      unfold szCond
      have := hQ.2.2.2.2.2.2.2
      nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (D.host.QS : ℝ) / 2),
        (by positivity : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d))]
    have h0 : 1 ≤ D.host.rdE := hQ.2.2.2.2.2.2.1
    have hc1 : 1 ≤ szCond L := h0.trans h1
    have h2 : szCond L ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      calc szCond L = szCond L ^ 1 * 1 := by ring
        _ ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
          mul_le_mul (pow_le_pow_right₀ hc1 (by norm_num)) (one_le_pow₀ hT.1) zero_le_one (by positivity)
    have hb : 1 ≤ L.sc.b := Real.one_le_exp hL.le
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h4 : D.host.rdE ≤ Real.exp L.sc.L := h1.trans (h2.trans (le_trans hC h3))
    have h5 : DimensionConstantBounds.lrd D ≤ L.sc.L := by
      unfold DimensionConstantBounds.lrd
      exact (Real.log_le_iff_le_exp (by linarith)).2 h4
    have h6 : |L.logDerivativeAtOne| ≤ L.sc.L := hL'
    linarith

theorem sizes_iff_of_sizesAt (L : SizeData₂ D) (h : SizesAt L) {C : ℝ} (hC : 2 * L.Ct ≤ C) :
    (WeightAlgebra.ParA L C ∧ (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ D.host.rdE ^ 3) ↔ DimensionConstantBounds.Sizes L C := by
  obtain ⟨r1, r2, r3⟩ := sizes_bounds_of_sizesAt L h
  constructor
  · rintro ⟨a, b⟩
    exact ((sizes_iff L C).1 ⟨a, r1, r2, b⟩).1
  · intro a
    exact ⟨((sizes_iff L C).2 ⟨a, fr_le L hC, r3⟩).1, a.2.2.2.2.2.2⟩

theorem compare {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (X : WeightFamilies.Prov D) :
    (WeightAlgebra.qq D = DimensionConstantBounds.q D ∧ WeightAlgebra.g0 D = DimensionConstantBounds.g0 D ∧
      (∀ (j : ℕ) (CP : ℝ) (w : WeightFamilies.Wt D j), WeightAlgebra.cc D L CP 12 7 w = DimensionConstantBounds.c L CP (DimensionConstantBounds.degF w)) ∧
      WeightAlgebra.lamStar D = DimensionConstantBounds.LamStar D ∧ WeightAlgebra.PN D L = DimensionConstantBounds.PN L ∧ (∀ j, WeightAlgebra.n0 D j = DimensionConstantBounds.n0 D j) ∧
      WeightAlgebra.Zb D L = DimensionConstantBounds.Z L ∧ WeightAlgebra.lrd D = DimensionConstantBounds.lrd D ∧ WeightAlgebra.PU D = DimensionConstantBounds.PU D ∧ WeightAlgebra.PO D L = DimensionConstantBounds.PO L ∧
      (∀ nW, WeightAlgebra.sizeConstantAtParamsWeight D nW = DimensionConstantBounds.sizeConstantAtWeight D nW) ∧ WeightAlgebra.sizeConstantAtParamsWeight D T.nWn = DimensionConstantBounds.sizeConstantAtParamsWeight T ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → WeightAlgebra.DivisibilityWeightConstant D j = DimensionConstantBounds.DivisibilityWeightConstant D) ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ PLam lNc, WeightAlgebra.PI4 D j PLam lNc = DimensionConstantBounds.PI4 D PLam lNc) ∧
      (∀ PLam po, WeightAlgebra.Gc L X PLam po = DimensionConstantBounds.G L X PLam po)) ∧
    (∀ CP, (∀ j, 1 ≤ j → j ≤ D.R.m → WeightAlgebra.DomAt D L j T.nWn CP) ↔ DimensionConstantBounds.Dom T CP) ∧
    (WeightAlgebra.OPO L X ↔ DimensionConstantBounds.RingBound L X) ∧
    (∀ C, (WeightAlgebra.ParA L C ∧ RowsSecond L) ↔ (DimensionConstantBounds.Sizes L C ∧ RowsFirst L C)) ∧
    (∀ CP C, ((∀ j, 1 ≤ j → j ≤ D.R.m → WeightAlgebra.DomAt D L j T.nWn CP) ∧ WeightAlgebra.OPO L X ∧ WeightAlgebra.ParA L C ∧ RowsSecond L) ↔
      (DimensionConstantBounds.Hyp T X CP C ∧ RowsFirst L C)) := by
  refine ⟨⟨q_eq D, g0_eq D, fun _ CP w => c_eq L CP w, lamStar_eq D, PN_eq L, normShift_eq D, Z_eq L, lrd_eq D, PU_eq D,
    PO_eq L, flipOneTwo_eq_sizeConstantAtWeight D, flipOneTwo_eq_sizeConstantAtWeight D _, fun _ => weight_constant_eq_dimension_constant D, fun _ => weightAlgebra_PI4_eq_dimensionConstant_PI4 D, G_eq L X⟩, dom_iff T, ring_iff L X,
    sizes_iff L, fun CP C => ?_⟩
  unfold DimensionConstantBounds.Hyp
  rw [dom_iff, ring_iff, sizes_iff]
  simp only [and_assoc]

end GlobalTheory.ConstCompare

end
