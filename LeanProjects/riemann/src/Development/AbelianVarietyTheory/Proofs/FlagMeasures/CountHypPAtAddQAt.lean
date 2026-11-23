import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem countHyp_one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (NumberField.discr_ne_zero I.E)
    exact_mod_cast h1
  show 1 ≤ |(discr I.E : ℝ)| ^ ((1 : ℝ) / (2 * (I.f : ℝ)))
  exact Real.one_le_rpow hd (by positivity)

theorem countHyp_card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero]
  exact (IsTotallyReal.finrank I.F).symm

theorem countHyp_pAt_add_qAt (I : AutInst) (v : InfinitePlace I.F) : I.pAt v + I.qAt v = I.n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin I.n)))
    (fun a => I.ε v a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem countHyp_numerics : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → 0 ≤ Cg ∧ 1 ≤ B.I.rd ∧ 1 ≤ B.I.f ∧ Fintype.card (InfinitePlace B.I.F) = B.I.f ∧ p + q = B.I.n ∧ 2 * q + 2 ≤ B.I.n ∧ (∀ v, rkR (B.I.ε v) = q) ∧ min p q = q ∧ 0 < (∏ v, d v) ∧ 16 ≤ bigX B b ∧ 0 < tauStar B q b ∧ (1 ≤ q → tauStar B q b < 1 / 2 ∧ (B.I.n : ℝ) ^ 19 ≤ b ^ 2) ∧ ∃ h : ℝ, h = 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) ∧ GapGe B h ∧ HBig B 40 h ∧ HBig B 32 h ∧ 8 * (B.I.n : ℝ) * q < h ∧ 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ h := by
  intro B Cg n₀ d p q b hn₀ hC
  unfold CountHyp at hC
  obtain ⟨hDS, hSig, hn, hq2, -, -, hb, -, hlam, hg1, hgC, -, -, -, hgap⟩ := hC
  have hrd : 1 ≤ B.I.rd := countHyp_one_le_rd B.I
  have hcard : Fintype.card (InfinitePlace B.I.F) = B.I.f := countHyp_card_places B.I
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hp₀, hq₀⟩ := hSig v₀
  have hpq : p + q = B.I.n := by rw [← hp₀, ← hq₀]; exact countHyp_pAt_add_qAt B.I v₀
  have h2q : 2 * q + 2 ≤ B.I.n := by
    rcases Nat.lt_or_ge q 3 with h | h
    · omega
    · nlinarith
  have hqp : q ≤ p := by omega
  have hmin : min p q = q := min_eq_right hqp
  have hrk : ∀ v, rkR (B.I.ε v) = q := by
    intro v
    obtain ⟨hp, hq⟩ := hSig v
    show min (B.I.pAt v) (B.I.qAt v) = q
    rw [hp, hq, hmin]
  have hd : 0 < ∏ v, d v := by
    refine Finset.prod_pos fun v _ => ?_
    obtain ⟨-, -, -, ⟨hdv, -⟩⟩ := hDS v
    exact hdv
  have hCg : 0 ≤ Cg := by
    by_contra hneg
    have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (lt_of_not_ge hneg)
    have h2 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
    linarith
  have hnr : (8 : ℝ) ≤ B.I.n := by exact_mod_cast le_trans hn₀ hn
  have hfr : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgr : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  have hX : 16 ≤ bigX B b := by
    show 16 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b
    have a1 : 8 ≤ (B.I.n : ℝ) * B.I.f := by nlinarith
    have a2 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd := by nlinarith
    have a3 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g := by nlinarith
    nlinarith
  have htpos : 0 < tauStar B q b := by
    show 0 < (bigX B b)⁻¹ ^ (11 * q)
    have : 0 < bigX B b := by linarith
    positivity

  have hL : Real.log 2 ≤ Real.log (b * B.I.rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog2 := Real.log_two_gt_d9
  have hF5 : (1 : ℝ) ≤ (B.I.f : ℝ) ^ 5 := one_le_pow₀ hfr
  have hP1 : 2 ≤ (Cg + 4) * Real.log (b * B.I.rd) := by nlinarith
  have hP : 2 ≤ (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = ((Cg + 4) * Real.log (b * B.I.rd)) * (B.I.f : ℝ) ^ 5 := by ring
    rw [this]
    nlinarith
  have hN : 0 ≤ (B.I.n : ℝ) ^ 19 := by positivity
  have hbig : 10 ^ 15 * (B.I.n : ℝ) ^ 19 ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = 8 * 10 ^ 14 * (B.I.n : ℝ) ^ 19 * ((Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)) := by
      ring
    rw [this]
    nlinarith
  have hn1 : (1 : ℝ) ≤ B.I.n := by linarith
  have hn2 : (B.I.n : ℝ) ^ 2 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn3 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hqn : (q : ℝ) ≤ B.I.n := by exact_mod_cast (show q ≤ B.I.n by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt q ≤ B.I.n := by
    calc Real.sqrt q ≤ Real.sqrt ((B.I.n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B.I.n := Real.sqrt_sq (by positivity)
  have hs40 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have e1 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (B.I.n : ℝ) ^ 2 * B.I.n :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 40 * (B.I.n : ℝ) ^ 2 * B.I.n = 40 * (B.I.n : ℝ) ^ 3 := by ring
    linarith
  refine ⟨hCg, hrd, hf, hcard, hpq, h2q, hrk, hmin, hd, hX, htpos, ?_, _, rfl, hgap, ?_, ?_, ?_, ?_, hs40⟩
  · intro hq1
    constructor
    · show (bigX B b)⁻¹ ^ (11 * q) < 1 / 2
      have hXp : 0 < bigX B b := by linarith
      have hi : (bigX B b)⁻¹ ≤ 16⁻¹ := inv_anti₀ (by norm_num) hX
      have hi0 : 0 ≤ (bigX B b)⁻¹ := inv_nonneg.mpr hXp.le
      have hpow : (bigX B b)⁻¹ ^ (11 * q) ≤ (bigX B b)⁻¹ :=
        pow_le_of_le_one hi0 (by linarith [show (16 : ℝ)⁻¹ ≤ 1 by norm_num]) (by omega)
      have : (16 : ℝ)⁻¹ < 1 / 2 := by norm_num
      linarith
    · have hpc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = true).card := by
        show 0 < B.I.pAt v₀
        omega
      have hqc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = false).card := by
        show 0 < B.I.qAt v₀
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpc
      obtain ⟨a', ha'⟩ := Finset.card_pos.mp hqc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
      have hne : B.I.ε v₀ a ≠ B.I.ε v₀ a' := by rw [ha, ha']; decide
      have hg := hgap v₀ a a' hne
      obtain ⟨l1, l2⟩ := abs_le.mp (hlam v₀ a)
      obtain ⟨l3, l4⟩ := abs_le.mp (hlam v₀ a')
      have hdiff : |B.lam v₀ a - B.lam v₀ a'| ≤ 2 * b ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb0 : 0 ≤ b ^ 2 := by positivity
      linarith
  · intro v
    rw [hrk v]
    linarith
  · intro v
    rw [hrk v]
    have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    nlinarith
  · have hpos : 0 < (B.I.n : ℝ) ^ 19 := by positivity
    have e1 : 8 * (B.I.n : ℝ) * q ≤ 8 * (B.I.n : ℝ) ^ 2 := by nlinarith
    linarith
  · have r1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hq0 hqn (by norm_num)
    have r2 : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_two] at r2
    have e1 : 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (r1.trans r2) (by positivity)
    have e2 : 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 = 120 * (B.I.n : ℝ) ^ 3 := by ring
    linarith

end GlobalTheory.Dec
