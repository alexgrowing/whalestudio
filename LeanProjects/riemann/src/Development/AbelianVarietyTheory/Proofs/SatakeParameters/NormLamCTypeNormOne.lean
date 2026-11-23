import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace

noncomputable section

namespace GlobalTheory.TwU.RatNorm

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem frob_pow_int (X : Sys p) (v : X.Pl) (k : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ k) (algebraMap _ _ x) = algebraMap _ _ y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ]
    show (X.G.P.σ v ^ k) ((X.G.P.σ v) (algebraMap _ _ x)) = _
    rw [hy, hz]

theorem norm_twG_int_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    ‖twG X E v s (algebraMap _ _ x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := frob_pow_int X v s.val x
  have h := E.int (X.G.P.j v y)
  unfold twG
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hy, (X.G.P.setting v).ι_comp]
  exact h

theorem norm_twG_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    ‖twG X E v s (algebraMap _ _ (u : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_int_le X E v s (u : X.G.P.W v)
  have h2 := norm_twG_int_le X E v s ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have h3 : twG X E v s (algebraMap _ _ (u : X.G.P.W v)) * twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg (twG X E v s (algebraMap _ _ (u : X.G.P.W v))),
    norm_nonneg (twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) {y : X.G.P.Qq v} (hy : y ≠ 0) :
    ‖twG X E v s y‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p y := by
  haveI := (X.G.P.setting v).frac_alt
  have hp := (X.G.P.setting v).p_unif
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  rw [ordP_eq hp n u, map_mul, map_zpow₀, map_natCast, norm_mul, norm_twG_unit, one_mul, norm_zpow]

theorem zpow_sum_fin {ι : Type*} (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (f : ι → ℤ) :
    r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hr, ih]

theorem norm_lamC_type_normOne : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
    LamPos X E pos lam ρ → ∀ (e : D.what₂.Tau → ℤ) (z : D.host.E), z * D.host.conj z = 1 →
    ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ)‖ =
      ‖(p : ℂ_[p])‖ ^ (∑ v : X.Pl, (∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩)) *
        ordP (X.G.P.W v) p (ρ v z)) := by
  intro D p _ X E pos lam ρ hL e z hz
  have hp0 : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hmem : ∀ τ, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hprod : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => zpow_mem (hmem τ) _
  have h1 : TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) = ∏ τ, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ z) ^ e τ := by
    have e1 : (⟨∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ, hprod⟩ : TaylorLogMetric.Qbar) = ∏ τ, (⟨TaylorLogMetric.embT D τ z, hmem τ⟩ : TaylorLogMetric.Qbar) ^ e τ := by
      apply Subtype.ext
      push_cast
      rfl
    unfold TaylorLogMetric.lamC
    rw [dif_pos hprod, e1, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [dif_pos (hmem τ), map_zpow₀]
  have hρ : ∀ v, ρ v z * ρ v (D.host.conj z) = 1 := fun v => by rw [← map_mul, hz, map_one]
  have hρ0 : ∀ v, ρ v z ≠ 0 := fun v h => by have := hρ v; rw [h, zero_mul] at this; exact zero_ne_one this
  have hf : ∀ v s, ‖TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) z)‖ ^ e (pos ⟨v, s⟩) =
      ‖(p : ℂ_[p])‖ ^ ((if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩) * ordP (X.G.P.W v) p (ρ v z)) := by
    intro v s
    by_cases hs : IsOddPos s
    · rw [LamPos.odd X E pos lam ρ hL v s hs, if_pos hs, eq_inv_of_mul_eq_one_right (hρ v), map_inv₀, norm_inv, norm_twG X E v s (hρ0 v),
        inv_zpow', ← zpow_mul]
      congr 1
      ring
    · rw [LamPos.even X E pos lam ρ hL v s hs, if_neg hs, norm_twG X E v s (hρ0 v), ← zpow_mul]
      congr 1
      ring
  rw [h1, norm_prod]
  simp_rw [norm_zpow]
  rw [← Equiv.prod_comp pos, Fintype.prod_sigma]
  simp_rw [hf, Finset.sum_mul]
  rw [zpow_sum_fin _ _ hp0]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [zpow_sum_fin _ _ hp0]

end GlobalTheory.TwU.RatNorm

end
