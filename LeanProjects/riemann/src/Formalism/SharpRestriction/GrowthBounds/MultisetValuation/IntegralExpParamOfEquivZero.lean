import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_logF_eq : logF p = lgF (K0 p) p := by
  ext n
  simp only [logF, lgF, PowerSeries.coeff_mk, pow_mul]

theorem sx_logF_const : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

def sx_lX {σ : Type} (i : σ) : MvPowerSeries σ (K0 p) :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)

private theorem constantCoeff_subst_X_logF_eq_zero {σ : Type} (i : σ) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [sx_logF_const]
  · simp [MvPowerSeries.constantCoeff_X, zero_pow hd.ne']

private theorem hs_lemma_2 {σ : Type} [Finite σ] :
    MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => constantCoeff_subst_X_logF_eq_zero p i)

theorem sx_inParam_X {σ : Type} [Finite σ] (i : σ) : inParam p (MvPowerSeries.X i) = sx_lX p i := by
  unfold inParam sx_lX
  exact MvPowerSeries.subst_X (hs_lemma_2 p) i

theorem sx_inParam_add {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f + g) = inParam p f + inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_add (hs_lemma_2 p) f g

theorem sx_inParam_mul {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f * g) = inParam p f * inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_mul (hs_lemma_2 p) f g

theorem sx_inParam_C_mul {σ : Type} [Finite σ] (a : K0 p) (g : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.C a * g) = MvPowerSeries.C a * inParam p g := by
  unfold inParam
  rw [MvPowerSeries.subst_mul (hs_lemma_2 p), MvPowerSeries.subst_C]

theorem sx_subst_ps {σ τ : Type} {a : σ → MvPowerSeries τ (K0 p)} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ (K0 p)} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries (K0 p)) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha f

theorem sx_inParam_subst {σ τ : Type} [Finite σ] [Finite τ] (a a' : σ → MvPowerSeries τ (K0 p))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, PowerSeries.subst (a' i) (logF p) = inParam p (a i)) (f : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.subst a f) = MvPowerSeries.subst a' (inParam p f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  unfold inParam
  rw [MvPowerSeries.subst_comp_subst_apply hA (hs_lemma_2 p), MvPowerSeries.subst_comp_subst_apply (hs_lemma_2 p) hA']
  congr 1
  funext s
  rw [sx_subst_ps p hA' (by simp) (logF p), MvPowerSeries.subst_X hA']
  exact (h s).symm

theorem sx_simeq_of {σ : Type} [Finite σ] {f g : MvPowerSeries σ (K0 p)} (h : Simeq p f g) :
    Formalism.InvariantFactorPaths.G7.Simeq (inParam p f) (inParam p g) := by
  obtain ⟨h0, w, _, hw⟩ := h
  have h1 : MvPowerSeries.constantCoeff (inParam p (f - g)) = 0 := th_inParam_const p h0
  rw [th_inParam_sub] at h1 hw
  refine ⟨h1, ?_⟩
  rw [← sx_expS_eq p h1, sx_integral_iff, hw]
  exact ⟨1 + w, by rw [map_add, map_one]⟩

theorem integralExp_of_equiv {σ : Type} {f g : MvPowerSeries σ (K0 p)} (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : E0 p (f - g) := by
  obtain ⟨h0, h1⟩ := h
  rw [← sx_expS_eq p h0, sx_integral_iff] at h1
  obtain ⟨w, hw⟩ := h1
  refine ⟨h0, w - 1, ?_, ?_⟩
  · have h2 : MvPowerSeries.constantCoeff (expS p (f - g)) = 1 := by
      rw [sx_expS_eq p h0]
      exact Formalism.InvariantFactorPaths.G7.DworkIntegrality.constantCoeff_mvExp h0
    rw [hw] at h2
    have h3 : algebraMap (WW p) (K0 p) (MvPowerSeries.constantCoeff w) = 1 := by
      rw [← h2, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_map]
    have h4 : MvPowerSeries.constantCoeff w = 1 :=
      IsFractionRing.injective (WW p) (K0 p) (by rw [h3, map_one])
    rw [map_sub, h4, map_one, sub_self]
  · show expS p (f - g) = _
    rw [hw, map_sub, map_one]
    ring

theorem equiv_zero_of_integralExp {σ : Type} {f : MvPowerSeries σ (K0 p)} (h : E0 p f) : Formalism.InvariantFactorPaths.G7.Simeq f 0 := by
  obtain ⟨h0, w, _, hw⟩ := h
  rw [Formalism.InvariantFactorPaths.G7.Simeq, sub_zero]
  refine ⟨h0, ?_⟩
  rw [← sx_expS_eq p h0, sx_integral_iff]
  exact ⟨1 + w, by rw [map_add, map_one]; exact hw⟩

theorem integralExp_param_of_equiv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ (K0 p)} (h : Simeq p f 0) : E0 p (inParam p f) := by
  have := integralExp_of_equiv p (sx_simeq_of p h)
  have e : inParam p (0 : MvPowerSeries σ (K0 p)) = 0 := by
    have := th_inParam_sub p (0 : MvPowerSeries σ (K0 p)) 0
    simpa using this
  rwa [e, sub_zero] at this

end Formalism.MainNotions.FormalGroupSystem.Pf
