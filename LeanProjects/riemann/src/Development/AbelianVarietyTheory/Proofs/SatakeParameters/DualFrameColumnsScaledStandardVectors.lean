import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem frameM_coef_eq_chgB : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D p _ lm ι hι X s n N N' a r cκ c0 P P' σ σ' hσ hσ' hdet hsum i x
  unfold frameM
  have hJ : ∀ f : GlobalTheory.DFrame.JJ D n N N' → ℂ_[p], ∑ j, f j = ∑ α, ∑ l, ∑ l', f (α, l, l') := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hJ, Fintype.sum_sigma]
  simp only [GlobalTheory.DFrame.coef, GlobalTheory.DFrame.gc, GlobalTheory.DFrame.pc]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Finset.sum_eq_single x.1 (fun z _ hz => by simp [hz]) (by simp)]
  simp only [if_true, GlobalTheory.DFrame.vecF, GlobalTheory.DFrame.mat, GlobalTheory.DFrame.colR, GlobalTheory.DFrame.rowL, Matrix.of_apply, map_mul, RingEquiv.coe_toRingHom]
  have hsum' := hsum x.1 (s.iT i.1)
  simp only [hι] at hsum'
  have e : ∀ k, ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k)) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (cκ x.1 * r x.1 k * (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) =
      (cκ x.1 * (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) *
      (r x.1 k * ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k))) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hsum']
  by_cases h : s.iT i.1 = tauPl D x.1
  · rw [if_pos h, TaylorLogMetric.chgB, if_pos h.symm]
    simp only [h]
    set tp := tauPl D x.1 with htp
    have hm : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin m) D.host.E),
        Q.map (TaylorLogMetric.tauEmb D lm tp) = Q.map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      intro m Q; ext u v; simp [hι]
    have hinv : ((P tp).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)))⁻¹ =
        ((P tp)⁻¹).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x.1)), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hm, hm, hinv]
    clear e hsum' hJ hsum hm hinv
    have h1 := hσ x.1
    have h2 := hσ' x.1
    simp only [GlobalTheory.DFrame.rho, RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1 h2 ⊢
    simp only [Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← htp] at h1 h2 ⊢
    field_simp
    try ring
  · rw [if_neg h, TaylorLogMetric.chgB, if_neg (fun e => h e.symm)]
    simp

end GlobalTheory.DFrame
