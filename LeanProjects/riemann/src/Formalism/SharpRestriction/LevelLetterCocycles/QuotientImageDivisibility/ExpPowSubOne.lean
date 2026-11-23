import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem div_exists {m : ℤ} {e : ℤ → V} (he : LB m e) (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) :
    ∃ d : ℤ → V, LB (m - K) d ∧ smulS ((X * u) ^ K) d = e := by
  set e' : ℤ → V := fun k => e (k + K) with he'
  have hLB' : LB (m - K) e' := fun k hk => he _ (by omega)
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  refine ⟨smulS (u ^ K)⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [mul_pow, smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ huK,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem div_unique {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (u : PowerSeries LL)
    (hu : constantCoeff u ≠ 0) (K : ℕ) (h : smulS ((X * u) ^ K) d = smulS ((X * u) ^ K) d') :
    d = d' := by
  have huK : constantCoeff (u ^ K) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu
  have h0 : smulS ((X * u) ^ K) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [mul_pow, smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS (u ^ K) (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + K)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') (u ^ K) huK
  rw [h1] at h2
  have h3 : smulS (u ^ K)⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

end Div

section Zero

variable {LL : Type} [Field LL]

theorem exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative LL E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E = 1 + X * E₁ := by
    refine ⟨PowerSeries.mk fun j => coeff (j + 1) E, ?_⟩
    have := PowerSeries.eq_X_mul_shift_add_const E
    rw [h0, map_one, add_comm] at this
    exact this
  have hc1 : constantCoeff E₁ = 1 := by
    have h1 := congrArg (coeff 0) hd
    rw [PowerSeries.coeff_derivative] at h1
    have h2 : coeff 1 E = constantCoeff E₁ := by
      rw [hE₁]; simp
    simp only [zero_add, Nat.cast_zero, mul_one, coeff_zero_eq_constantCoeff_apply, h0] at h1
    rw [← h2]
    simpa using h1
  refine ⟨E₁ * ∑ j ∈ Finset.range p, (1 + X * E₁) ^ j, ?_, ?_⟩
  · rw [hE₁, ← mul_assoc]
    have g := geom_sum_mul (1 + X * E₁) p
    rw [add_sub_cancel_left] at g
    rw [← g, mul_comm]
  · rw [map_mul, map_sum, hc1, one_mul]
    simp [map_pow]

end Zero

section Simple

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

theorem lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  have hp0 : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have hπq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [letπ, LocWach.q, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hl := congrArg (W.lev c ζ) hπq
  rw [map_mul, map_sub, map_pow, map_add, map_one] at hl
  rw [hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul] at hl
  obtain ⟨w, hw, hw0⟩ := exp_pow_sub_one E hE0 hEd PD.p
  rw [hw] at hl
  have hπc : constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have := congrArg constantCoeff hE
    rw [map_add, map_one, map_mul, constantCoeff_C, hE0, mul_one] at this
    intro h0
    rw [h0, add_zero] at this
    exact hζ1 this.symm
  refine ⟨w * (W.lev c ζ letπ)⁻¹, ?_, ?_⟩
  · have h2 : W.lev c ζ letπ * W.lev c ζ W.q * (W.lev c ζ letπ)⁻¹ =
        X * w * (W.lev c ζ letπ)⁻¹ := by rw [hl]
    rw [mul_comm (W.lev c ζ letπ), mul_assoc, PowerSeries.mul_inv_cancel _ hπc, mul_one] at h2
    rw [h2, mul_assoc]
  · rw [map_mul, hw0, PowerSeries.constantCoeff_inv]
    exact mul_ne_zero hp0 (inv_ne_zero hπc)

end Simple

end Formalism.MainNotions.N.Pv.LocalLengthBound
