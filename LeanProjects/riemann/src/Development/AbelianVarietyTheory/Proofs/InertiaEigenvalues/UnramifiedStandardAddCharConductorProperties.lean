import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.StdChar

def qe (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

theorem qe_add (a b : ℚ) : qe (a + b) = qe a * qe b := by
  simp only [qe, Rat.cast_add, mul_add, Complex.exp_add]

theorem qe_int (n : ℤ) : qe n = 1 := by
  simp only [qe, Rat.cast_intCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem qe_eq_one {q : ℚ} (h : qe q = 1) : ∃ n : ℤ, q = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (q : ℂ) = n := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast this

def ce (z : AddCircle (1 : ℚ)) : ℂ :=
  Quotient.liftOn' z qe (fun a b h => by
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨n, hn⟩ := h
    have hb : b = a + n := by rw [zsmul_one] at hn; linarith
    rw [hb, qe_add, qe_int, mul_one])

theorem ce_coe (q : ℚ) : ce (q : AddCircle (1 : ℚ)) = qe q := rfl

theorem ce_add (a b : AddCircle (1 : ℚ)) : ce (a + b) = ce a * ce b := by
  induction a using QuotientAddGroup.induction_on with
  | H a =>
  induction b using QuotientAddGroup.induction_on with
  | H b =>
  rw [← QuotientAddGroup.mk_add]
  exact qe_add a b

theorem ce_zero : ce 0 = 1 := by
  rw [show (0 : AddCircle (1 : ℚ)) = ((0 : ℚ) : AddCircle (1 : ℚ)) by simp, ce_coe]
  simpa using qe_int 0

theorem ce_eq_one {z : AddCircle (1 : ℚ)} (h : ce z = 1) : z = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H q =>
  obtain ⟨n, hn⟩ := qe_eq_one h
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [hn]⟩

section Field
variable {F : Type} [NontriviallyNormedField F]

def intSub (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] : AddSubgroup F where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem mem_intSub [IsUltrametricDist F] {x : F} : x ∈ intSub F ↔ ‖x‖ ≤ 1 := Iff.rfl

def charOf (c : F →+ AddCircle (1 : ℚ)) : AddChar F ℂ where
  toFun x := ce (c x)
  map_zero_eq_one' := by simp [ce_zero]
  map_add_eq_mul' a b := by simp [ce_add]

theorem exists_unif [IsUltrametricDist F] [ProperSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨z, hz0, hz1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle z hz1
  rw [h, norm_zero] at this
  linarith

theorem exists_nat_norm_lt_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] :
    ∃ N : ℕ, 0 < N ∧ ‖(N : F)‖ < 1 := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq
    (x := fun n : ℕ => (n : F)) (fun n => by simpa using IsUltrametricDist.norm_natCast_le_one F n)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h := hM (M + 1) (by omega)
  have hlt : φ M < φ (M + 1) := hφ (by omega)
  refine ⟨φ (M + 1) - φ M, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le, ← dist_eq_norm]
  simpa using h

variable (F) in
theorem exists_stdChar [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by
  obtain ⟨ϖ, hϖ0, hϖ1, hle⟩ := exists_unif (F := F)
  have hpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hx : (QuotientAddGroup.mk ϖ⁻¹ : F ⧸ intSub F) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, mem_intSub, norm_inv, not_le]
    exact one_lt_inv_iff₀.2 ⟨hpos, hϖ1⟩
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : F →+ AddCircle (1 : ℚ) := AddMonoidHom.comp c (QuotientAddGroup.mk' (intSub F))
  refine ⟨charOf c', fun x hx1 => ?_, ϖ⁻¹, fun h => hc ?_, fun y hy => ?_⟩
  · show ce (c (QuotientAddGroup.mk x)) = 1
    rw [(QuotientAddGroup.eq_zero_iff x).2 hx1, map_zero, ce_zero]
  · exact ce_eq_one h
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hle y hy

end Field

section Props
variable {F : Type} [NontriviallyNormedField F]

theorem locConst [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun x' hx' => ?_⟩
  have h : ψ (x' - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx').le)
  calc ψ x' = ψ (x + (x' - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h, mul_one]

theorem norm_eq_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] {ψ : AddChar F ℂ}
    (hψ : IsStdChar ψ) (x : F) : ‖ψ x‖ = 1 := by
  obtain ⟨N, hN0, hN1⟩ := exists_nat_norm_lt_one (F := F)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxpos) hN1
  have h1 : ψ ((N ^ k : ℕ) • x) = 1 := by
    apply hψ.1
    rw [nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    exact (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)).trans (by rw [inv_mul_cancel₀ hxpos.ne'])
  rw [AddChar.map_nsmul_eq_pow] at h1
  have h2 : ‖ψ x‖ ^ (N ^ k) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hN0.ne')).1 h2

theorem conductor [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F) :
    (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy y⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy)
      rwa [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul] at this
    apply hx
    have := h (x * y⁻¹) (by rw [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  · intro hy e he
    exact hψ.1 _ (by rw [norm_mul]; exact mul_le_one₀ he (norm_nonneg _) hy)

end Props

section Ext
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem conductor_trace [hU : Unram F E]
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (he : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1)
    {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : E) :
    (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  haveI := hU.ultraE
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    obtain ⟨e₀, he₀, hsum⟩ := he
    obtain ⟨a, ha⟩ := hU.unram y
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ha1 : 1 < ‖a‖ := ha ▸ hy
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha1; linarith
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy a⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ha1)
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.2 ha0), one_mul] at this
      rwa [ha]
    have htr1 : Algebra.trace F E e₀ = 1 := by
      apply (algebraMap F E).injective
      rw [htr, hsum, map_one]
    apply hx
    have := h (algebraMap F E x * e₀ * y⁻¹) (by
      rw [norm_mul, norm_mul, norm_inv, norm_algebraMap', mul_inv_le_iff₀ hypos]
      calc ‖x‖ * ‖e₀‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left he₀ (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by rw [mul_one, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one, ← Algebra.smul_def, LinearMap.map_smul, htr1,
      smul_eq_mul, mul_one] at this
  · intro hy e he'
    apply hψ.1
    have hz : ‖e * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ he' (norm_nonneg _) hy
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz (by rw [hU.norm_star]; exact hz))

end Ext

theorem psi_conductor : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ →
    IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧
    (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧
    ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  intro F E _ _ _ _ hU
  haveI := hU.ultraF
  haveI := hU.charZero
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨htr, he, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  exact ⟨exists_stdChar F, fun ψ hψ => ⟨locConst hψ, norm_eq_one hψ, conductor hψ,
    conductor_trace htr he hψ⟩⟩

end GlobalTheory.StdChar
