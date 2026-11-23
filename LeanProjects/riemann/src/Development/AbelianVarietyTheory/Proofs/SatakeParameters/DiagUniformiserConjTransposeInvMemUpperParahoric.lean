import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConj

open Matrix
open Formalism.UG (bc GLint)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem inv_val_of_diagonal {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0) :
    (d⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun i => (D i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  exact mul_inv_cancel₀ (hD i)

theorem conj_diag_apply {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0)
    (g : GL (Fin n) K) (p q : Fin n) : (d * g * d⁻¹).val p q = D p * g.val p q * (D q)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, inv_val_of_diagonal hd hD, hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_GLint_of {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) :
    x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable (v : Valuation K (WithZero (Multiplicative ℤ))) {r : ℕ} {ϖ : K}

theorem conj_le_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (h2 : ∀ q p : Fin n, p.val < r → q ≠ p → v (M q p) < 1) (p q : Fin n) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_mul, map_inv₀]
  by_cases hp : (p : ℕ) < r <;> by_cases hq : (q : ℕ) < r <;>
    simp only [hp, hq, if_true, if_false, map_one, inv_one, one_mul, mul_one, hϖ]
  · exact h1 q p
  · have hqp : q ≠ p := fun e => hq (e ▸ hp)
    calc v (M q p) * (WithZero.exp (-1))⁻¹ ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ :=
          mul_le_mul' (le_exp_neg_one_of_lt_one (h2 q p hp hqp)) le_rfl
      _ = 1 := mul_inv_cancel₀ hne
  · calc WithZero.exp (-1) * v (M q p) ≤ 1 * 1 := mul_le_mul' exp_neg_one_lt_one.le (h1 q p)
      _ = 1 := one_mul 1
  · rw [mul_comm (WithZero.exp (-1)), mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact h1 q p

theorem conj_lower_lt_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (p q : Fin n) (hp : r ≤ p.val) (hq : q.val < r) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) < 1 := by
  rw [if_neg (not_lt.2 hp), if_pos hq, inv_one, mul_one, map_mul, hϖ]
  calc WithZero.exp (-1) * v (M q p) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (h1 q p)
    _ < 1 := by rw [mul_one]; exact exp_neg_one_lt_one

end Pure

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem valued_lt_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem valued_le_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem facts_of_mem (s : SplitPlace L) (r t : ℕ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (a : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)))
    (ha : Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t) :
    (∀ i j, Valued.v (a.val i j) ≤ 1) ∧
      ∀ q p : Fin (r + t), p.val < r → Valued.v (a.val q p - if q = p then 1 else 0) < 1 := by
  obtain ⟨hK, hcol⟩ := ha
  refine ⟨fun i j => ?_, fun q p hp => ?_⟩
  · have := val_le_one_of_mem_KO hK i j
    rw [valued_le_one_iff_w] at this
    simpa [hc] using this
  · have := hcol q ⟨p, hp⟩
    have e : Fin.castAdd t (⟨p, hp⟩ : Fin r) = p := Fin.ext rfl
    rw [e, valued_lt_one_iff_w] at this
    have e2 : ((Matrix.GeneralLinearGroup.map c.toRingHom a).val - 1) q p =
        c (a.val q p - if q = p then 1 else 0) := by
      by_cases h : q = p <;> simp [Matrix.one_apply, h]
    rw [e2, hc] at this
    exact this

end Place

end GlobalTheory.BlockConj

namespace GlobalTheory.BlockConj

open Formalism.UG (GLint)

theorem conj_transpose_inv_uniRT : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  intro L _ _ _ s r t c hc a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hD : ∀ i : Fin (r + t), (if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) ≠ 0 := by
    intro i; split_ifs
    · exact one_ne_zero
    · exact hϖ0
  obtain ⟨ha1, ha2⟩ := facts_of_mem s r t c hc a ha
  obtain ⟨hi1, hi2⟩ := facts_of_mem s r t c hc a⁻¹ (by rw [map_inv]; exact (blockGrp _ r t).inv_mem ha)
  have ha2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v (a.val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using ha2 q p hp
  have hi2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v ((a⁻¹).val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using hi2 q p hp
  have hbinv : (b⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val = a.val.transpose := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hb, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hN : ∀ p q, (d * b * d⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * (a⁻¹).val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    intro p q; rw [conj_diag_apply hd hD, hb, Matrix.transpose_apply]
  have hNi : ∀ p q, ((d * b * d⁻¹)⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * a.val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    have e : (d * b * d⁻¹)⁻¹ = d * b⁻¹ * d⁻¹ := by group
    intro p q; rw [e, conj_diag_apply hd hD, hbinv, Matrix.transpose_apply]

  have hUL : ∀ p q : Fin (r + t), p.val < r → q.val < r → (d * b * d⁻¹).val p q = (a⁻¹).val q p := by
    intro p q hp hq; rw [hN, if_pos hp, if_pos hq, inv_one, one_mul, mul_one]
  refine ⟨⟨⟨mem_GLint_of (fun i j => ?_) (fun i j => ?_), fun p q hp hq => ?_⟩, fun p q hp hq => ⟨fun hlt => ?_, fun he => ?_⟩⟩, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hN]
    exact conj_le_one Valued.v hϖ hi1 hi2' i j
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hNi]
    exact conj_le_one Valued.v hϖ ha1 ha2' i j
  · rw [hN]; exact conj_lower_lt_one Valued.v hϖ hi1 p q hp hq
  · rw [hUL p q hp hq]; exact hi2' q p hp (Fin.ne_of_lt hlt)
  · subst he; rw [hUL p p hp hp]; simpa using hi2 p p hp
  · unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · rw [hUL p q (by omega) h.2]
      exact hi2' q p (by omega) (fun e => by rw [e] at h; omega)
    · rw [map_zero]; exact zero_lt_one

end GlobalTheory.BlockConj
