import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeCoordAddAndComplexMulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Norm

variable {q : ℕ} [hq : Fact q.Prime]

lemma cc_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    constantCoeff (f.subst a : ℂ_[q]⟦X⟧) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

lemma coeff_expY_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    coeff 1 (f.subst a : ℂ_[q]⟦X⟧) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, cc_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

lemma const_log (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hat_scale (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  have hs : HasSubst (C ω * logS : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' (const_log ω)
  unfold hat
  rw [subst_comp_subst_apply hs hsub, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul,
    map_mul, mul_assoc]

lemma mchart_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} (ha : ‖a‖ = 1) :
    M.MChart (ω * zc a) := by
  obtain ⟨hm, -, -, hb, -, hn⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, h1, -⟩ := hm a
  obtain ⟨ok, -, bd, c1⟩ := h
  refine ⟨ok, const_log _, ?_, ?_⟩
  · rw [hat_scale, hb a _ _ ha]; exact bd
  · rw [hat_scale, coeff_expY_subst h0, norm_mul, c1, h1, hn, ha, one_mul]

lemma at_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} {ξ : ℂ_[q]} {n k : ℕ} {y : ℂ}
    (hξ : ξ ^ (q ^ n) = 1) (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hy : M.At ω (ξ ^ k) y) :
    M.At (ω * zc a) ξ y := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, -⟩ := hm a
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ξ n k a _ hξ hk ⟨1, h.2.2.1⟩
  obtain ⟨s, h3, h4⟩ := hy
  refine ⟨s, h1, ?_⟩
  rw [hat_scale, ← (Shift.shift_laws q ξ h1).2.2.2.2.1, h2, cc_subst h0,
    (Shift.shift_laws q _ h3).2.2.2.2.1, h4]

lemma at_pow (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {ξ : ℂ_[q]} {p : ℂ} (hp : M.At ω ξ p) (k : ℕ) :
    M.At ω (ξ ^ k) ((k : ℂ) * p) := by
  induction k with
  | zero => simpa using (GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h).2.2.2.2
  | succ k ih =>
    have := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).1 _ _ _ _ ih hp
    rw [← pow_succ] at this
    convert this using 1
    push_cast; ring

noncomputable def rt (q n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((q ^ n : ℕ) : ℂ))

lemma rt_prim (n : ℕ) : IsPrimitiveRoot (rt q n) (q ^ n) :=
  Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hq.out.ne_zero)

lemma rt_succ (n : ℕ) : rt q (n + 1) ^ q = rt q n := by
  unfold rt
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  push_cast
  field_simp
  ring

lemma kap_eq {d : ℕ} (hd : 0 < d) (n : ℕ) (u b : ℤ) :
    kap1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) = rt q n ^ b := by
  unfold kap1 rt
  rw [← Complex.exp_int_mul]
  congr 1
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have : (h1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n)).im = -(b : ℝ) / (q : ℝ) ^ n := by
    unfold h1
    have e : ((q : ℂ) ^ n) = (((q : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [e, one_mul, Complex.im_ofReal_mul, Complex.conj_im, Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re, OKArith.im_w]
    field_simp
    ring
  rw [this]
  push_cast
  ring

lemma norm_qpow (n : ℕ) : ‖(q : ℂ_[q]) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have := OKArith.norm_zc (q := q) ((q : ℤ_[q]) ^ n)
  rw [PadicInt.norm_p_pow] at this
  simpa using this

lemma pow_le (n m : ℕ) (h : n ≤ m) : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := by
  have : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  exact zpow_le_zpow_right₀ this (by omega)

section
variable {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (hs : Split d q)
include hd h16 hs

lemma norm_le (ι : ℂ ≃+* ℂ_[q]) {α : ℂ} (h : InOK d α) : ‖ι α‖ ≤ 1 := by
  obtain ⟨⟨a, ha⟩, -⟩ := (okArith d q ι hd h16 hs).2.1 α h
  rw [ha, OKArith.zc_eq, OKArith.norm_zc]
  exact PadicInt.norm_le_one a

lemma div_ok (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (u b : ℤ) (hb : (q : ℤ) ^ n ∣ b)
    (hc : ‖ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ))) :
    InOK d (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) := by
  refine (okArith d q ι hd h16 hs).2.2.1 _ n ⟨u, b, rfl⟩ ?_ hc
  obtain ⟨c, rfl⟩ := hb
  have h1 : ‖ι (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d)‖ ≤ 1 := norm_le hd h16 hs ι ⟨_, _, rfl⟩
  have e : (u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d =
      conj ((u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d) +
        (q : ℂ) ^ n * (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d) := by
    rw [OKArith.conj_el]; push_cast; ring
  rw [e, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc ?_)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_qpow]
  exact mul_le_of_le_one_right (by positivity) h1

lemma gen (M : Mdl q) {ω : ℂ_[q]} (hL : IsOK d M.L) (h : M.MChart ω) (n : ℕ) :
    ∃ u b : ℤ, M.At ω (M.ι (rt q n)) (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) ∧
      ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ (n ≠ 0 → ¬ (q : ℤ) ∣ b) := by
  obtain ⟨hex, -, huq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  obtain ⟨⟨-, -, hring⟩, hint, -, hid, -⟩ := okArith d q M.ι hd h16 hs
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hη : M.ι (rt q n) ^ (q ^ n) = 1 := by rw [← map_pow, (rt_prim n).pow_eq_one, map_one]
  have hlt : ‖M.ι (rt q n) - 1‖ < 1 :=
    ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n 0 0 0 hη (by simp) ⟨0, fun m => by simp⟩).1
  obtain ⟨p, hp⟩ := hex _ hlt
  have kill : ∀ z, M.At ω 1 z ↔ InOK d z := fun z => by
    rw [hlat 1 0 z h10, zero_sub, neg_mem_iff, hL]
  have h1 := at_pow M h hp (q ^ n)
  rw [hη, kill] at h1
  obtain ⟨u, b, hub⟩ := h1
  have hpe : p = ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n := by
    rw [← hub]; push_cast; field_simp
  have hc : ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    obtain ⟨e, he, he1, he2⟩ := hid (n + 1) 1 (by simp)
    have hce := (hring e e he he).2.2.2
    obtain ⟨⟨a, ha⟩, -⟩ := hint _ hce
    have h2 := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).2 (conj e) a n 0 _ p
      (fun l hl => (hL _).2 (hring _ _ hce ((hL _).1 hl)).2.1) ha
      (by
        rw [Nat.cast_zero, sub_zero, ← OKArith.norm_zc, ← OKArith.zc_eq, ← ha]
        exact he2.trans (pow_le _ _ (by omega))) hη hp
    rw [pow_zero, kill] at h2
    have h3 := norm_le hd h16 hs M.ι (hring _ _ h2 h2).2.2.2
    have hne : ‖M.ι e‖ = 1 := by
      rw [Nat.cast_one, one_mul] at he1
      have : ‖M.ι e - 1‖ < ‖(1 : ℂ_[q])‖ := by
        rw [norm_one]
        exact he1.trans_lt (zpow_lt_one_of_neg₀ hq1 (by omega))
      have h5 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this.ne
      rw [sub_add_cancel, max_eq_right this.le, norm_one] at h5
      exact h5
    have e1 : e * conj ((u : ℂ) + (b : ℂ) * wK d) = (q : ℂ) ^ n * conj (conj e * p) := by
      rw [← hub]; simp only [map_mul, Complex.conj_conj, map_natCast]; push_cast; ring
    have e2 := congrArg (fun z => ‖M.ι z‖) e1
    simp only [map_mul M.ι, norm_mul, hne, one_mul, map_pow M.ι, map_natCast, norm_qpow] at e2
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) h3
  refine ⟨u, b, hpe ▸ hp, hc, fun hn hb => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h4 := div_ok hd h16 hs M.ι 1 u b (by simpa using hb) (hc.trans (pow_le _ _ (by omega)))
  have e3 : ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ 1 = ((q ^ m : ℕ) : ℂ) * p := by
    rw [hpe, Nat.succ_eq_add_one]; push_cast; field_simp; ring
  rw [e3, ← kill] at h4
  have h5 := huq _ _ _ (at_pow M h hp (q ^ m)) h4
  rw [← map_pow, ← map_one M.ι] at h5
  have h6 := (rt_prim (q := q) (m + 1)).dvd_of_pow_eq_one _ (M.ι.injective h5)
  have := (Nat.pow_dvd_pow_iff_le_right hq.out.one_lt).1 h6
  omega

end

theorem exists_normalised_chart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  intro d q hq M ω hd h16 hs hL h
  choose u b hat hc hb using gen hd h16 hs M hL h
  obtain ⟨-, -, -, hlat, -⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdv : ∀ n, (q : ℤ) ^ n ∣ b (n + 1) - b n := fun n => by
    have h1 := at_pow M h (hat (n + 1)) q
    rw [← map_pow, rt_succ] at h1
    obtain ⟨s, t, hst⟩ := (hL _).1 ((hlat _ _ _ h1).1 (hat n))
    have : ((u (n + 1) - u n : ℤ) : ℂ) + ((b (n + 1) - b n : ℤ) : ℂ) * wK d =
        (((q : ℤ) ^ n * s : ℤ) : ℂ) + (((q : ℤ) ^ n * t : ℤ) : ℂ) * wK d := by
      push_cast
      have e : (q : ℂ) ^ n * s + (q : ℂ) ^ n * t * wK d = (q : ℂ) ^ n * ((s : ℂ) + t * wK d) := by ring
      rw [e, ← hst]
      field_simp
      ring
    exact ⟨t, (OKArith.coord_unique hd.pos this).2⟩
  set β : ℤ_[q] := PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub b q hdv) with hβ
  have hβn : ∀ n, PadicInt.toZModPow n β = b n :=
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub b q hdv
  have hβu : IsUnit β := by
    by_contra hu
    have h1 : ‖β‖ < 1 := PadicInt.not_isUnit_iff.1 hu
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := hβn 1
    rw [hc, map_mul, map_natCast] at h2
    have h3 : ((q : ℕ) : ZMod (q ^ 1)) = 0 := by rw [ZMod.natCast_eq_zero_iff]; simp
    rw [h3, zero_mul, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    exact hb 1 one_ne_zero (by simpa using h2)
  obtain ⟨a, ha⟩ := hβu.exists_left_inv
  have hna : ‖a‖ = 1 := PadicInt.isUnit_iff.1 (IsUnit.of_mul_eq_one _ ha)
  refine ⟨a, hna, mchart_scale M h hna, ?_⟩
  rintro n y ⟨v, ⟨s, t, rfl⟩, hv, rfl⟩
  rw [Nat.cast_one, one_mul, kap_eq hd.pos]
  have hqn : 0 < q ^ n := pow_pos hq.out.pos n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = t % ((q ^ n : ℕ) : ℤ) :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hqn.ne'))⟩
  have hrt : rt q n ^ t = rt q n ^ k := by
    have h0 : rt q n ≠ 0 := Complex.exp_ne_zero _
    conv_lhs => rw [← Int.emod_add_mul_ediv t ((q ^ n : ℕ) : ℤ), ← hk]
    rw [zpow_add₀ h0, zpow_mul, zpow_natCast, zpow_natCast, (rt_prim n).pow_eq_one, one_zpow, mul_one]
  have hξ : M.ι (rt q n ^ t) ^ (q ^ n) = 1 := by
    rw [hrt, ← map_pow, ← pow_mul, mul_comm, pow_mul, (rt_prim n).pow_eq_one, one_pow, map_one]
  refine ⟨hξ, at_scale M h (k := a.appr n) hξ ?_ ?_⟩
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    exact PadicInt.appr_spec n a
  · have h1 := at_pow M h (hat n) (k * a.appr n)
    rw [hrt, map_pow, ← pow_mul]
    refine (hlat _ _ _ h1).2 ((hL _).2 ?_)
    have hz : (q : ℤ) ^ n ∣ (k * a.appr n : ℕ) * b n - t := by
      have e1 : ((a.appr n : ℕ) : ZMod (q ^ n)) * (b n : ZMod (q ^ n)) = 1 := by
        rw [← hβn, show ((a.appr n : ℕ) : ZMod (q ^ n)) = PadicInt.toZModPow n a from rfl, ← map_mul, ha,
          map_one]
      have e2 : ((k : ℕ) : ZMod (q ^ n)) = (t : ZMod (q ^ n)) := by
        rw [← Int.cast_natCast, hk, ZMod.intCast_mod]
      have : ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ZMod (q ^ n)) = 0 := by
        push_cast
        rw [mul_assoc, e1, e2, mul_one, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    have h2 := div_ok hd h16 hs M.ι n ((k * a.appr n : ℕ) * u n - s) _ hz (by
      have e : conj (((((k * a.appr n : ℕ) : ℤ) * u n - s : ℤ) : ℂ) +
          ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ℂ) * wK d) =
          ((k * a.appr n : ℕ) : ℂ) * conj ((u n : ℂ) + (b n : ℂ) * wK d) +
            - conj ((s : ℂ) + (t : ℂ) * wK d) := by
        simp only [OKArith.conj_el]; push_cast; ring
      rw [e, map_add, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [map_mul, map_natCast, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans (hc n)
      · rw [norm_neg]
        refine hv.trans ?_
        have := pow_le (q := q) n (2 * n) (by omega)
        simpa using this)
    convert h2 using 1
    push_cast
    ring

end GlobalTheory.MomOne.Norm
