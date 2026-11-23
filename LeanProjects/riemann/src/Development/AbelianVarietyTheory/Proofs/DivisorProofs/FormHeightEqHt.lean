import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightTieProof

theorem formHeight_eq_ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) :
    formHeight δ w A f = ht w A f + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  have hr : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold ht formHeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  field_simp
  ring

theorem ht_pow (hM : HtMul) {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (e : ℕ) :
    ht w A (f ^ e) = e * ht w A f := by
  induction e with
  | zero =>
    have := (hM F B N n w A Λ hL).2 1 one_ne_zero
    simpa using this
  | succ k ih =>
    have hk : IsMultiHomogeneous (k • a) (f ^ k) :=
      isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 ha).pow k)
    rw [pow_succ, (hM F B N n w A Λ hL).1 (k • a) a _ _ (pow_ne_zero k hf) hf hk ha, ih]
    push_cast; ring

theorem heightTie : HtMul → HeightTie := by
  intro hM F _ _ T Λ hL h hh d e f c hf he hc
  obtain ⟨d', f', -, hf', e'⟩ := hh
  obtain ⟨rfl, c', hc', rfl⟩ := hf.isChowFormInt.unique hf'.isChowFormInt
  have hf0 := hf.isChowFormInt.ne_zero
  have hd := hf.isChowFormInt.pos
  rw [HeightUnique.formHeight_C_mul hL.pos d hL.spans hL.det hf0 hf.homog hc', formHeight_eq_ht] at e'
  have hpow : IsMultiHomogeneous (e • fun _ => d) (f ^ e) :=
    isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 hf.homog).pow e)
  have key : ht T.w T.A (C c * f ^ e) = e * ht T.w T.A f := by
    unfold ht
    rw [HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det (pow_ne_zero e hf0) hpow hc]
    exact ht_pow hM hL hf0 hf.homog e
  have hD : (0 : ℝ) < (T.D : ℝ) + 1 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have eq1 : ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) =
      h - (harmonic (T.N - 1) : ℝ) / 2 := by
    rw [key, div_eq_iff (by push_cast; positivity)]
    push_cast
    push_cast at e'
    have : ht T.w T.A f = ((T.D : ℝ) + 1) * d * h - ((T.D : ℝ) + 1) * d * (harmonic (T.N - 1) : ℝ) / 2 := by
      linarith
    rw [this]; ring
  refine ⟨eq1, ?_⟩
  rw [eq1]

  have hNn : T.N ≤ T.n := by
    have h1 := finrank_range_le_card (R := F) (b := T.w.col)
    rw [Set.finrank, hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hH : (harmonic (T.N - 1) : ℝ) ≤ 1 + Real.log (T.N - 1 : ℕ) := harmonic_le_one_add_log _
  have hlog : Real.log (T.N - 1 : ℕ) ≤ Real.log T.n := by
    rcases Nat.eq_zero_or_pos (T.N - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : T.N - 1 ≤ T.n))
  linarith

end GlobalTheory.HeightTieProof
