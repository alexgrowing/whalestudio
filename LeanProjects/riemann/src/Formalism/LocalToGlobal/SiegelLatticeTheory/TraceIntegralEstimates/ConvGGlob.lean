import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGGG
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralFinProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.S.Pv.ConvG

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocQuadGG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ (v : InfinitePlace X.B.I.F) (cv : Fin (D.R.rS + 1) → ℂ),
      cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u' → ∀ g : Formalism.REAL.UJ (X.B.I.ε v),
        Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal cv →
        ∫⁻ x, ∫⁻ y, ‖⟪X.B.σ v (uMat x) (X.B.w v), X.B.σ v (uMat g) (X.B.σ v (uMat y) (X.B.w v))⟫_ℂ‖ₑ *
          ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def StepConv1 : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : D.what₂.Word),
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
      ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

section Glob

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

private theorem norm_psiR_eq_one {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ)
    (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  unfold psiR
  have hS : (∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a))) =
      ((∑ a, 2 * (rootCoord ε e f z g a).re : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.add_conj]
    push_cast
    ring
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (∑ a, 2 * (rootCoord ε e f z g a).re) / gg) using 2
  rw [hS]
  push_cast
  ring_nf

private theorem norm_psiInf_eq_one (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (g : ℕ) (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (s : I.Ginf) : ‖psiInf I g e f z s‖ = 1 := by
  unfold psiInf
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiR_eq_one _ _ _ _ _ _

theorem norm_Wu_S (u : D.what₂.Word) : ∀ s ∈ X.SinfU u, ∀ x, ‖X.Wu u (s * x)‖ = ‖X.Wu u x‖ := by
  intro s hs x
  rw [(X.Wu_spec u).1 s hs x, norm_smul, norm_psiInf_eq_one, one_mul]
  have h := (X.piU_rep u).2.2.1 s hs (X.Wu u x) (X.Wu u x)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖X.piU u s (X.Wu u x)‖ ^ 2 = ‖X.Wu u x‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

@[irreducible] def phiV (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ℝ≥0∞ :=
  ‖⟪X.B.σ v (uMat a) (X.B.w v), X.B.σ v (uMat (γ v)) (X.B.σ v (uMat b) (X.B.w v))⟫_ℂ‖ₑ *
    ‖X.Wloc u v a‖ₑ * ‖X.Wloc u' v b‖ₑ

private theorem nnnorm_tensU_eq_prod (u : D.what₂.Word) (a : ∀ v, X.Vloc u v) :
    ‖X.tensU u a‖₊ = ∏ v, ‖a v‖₊ := by
  have h := X.tensU_inner u a a
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖X.tensU u a‖ ^ 2 = (∏ v, ‖a v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  have h3 := (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg (a v))
    two_ne_zero).1 h2
  ext
  push_cast
  exact h3

theorem phiGG_eq (u u' : D.what₂.Word) (γ x y : X.B.I.Ginf) :
    PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y = ∏ v, phiV X u u' γ v (x v) (y v) := by
  obtain ⟨hin, hσ, -⟩ := X.B.tens_spec
  unfold PhiGG phiV
  simp only [hσ, hin, X.Wu_tens, enorm_eq_nnnorm, nnnorm_prod, nnnorm_tensU_eq_prod, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]

theorem measurable_phiV (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => phiV X u u' γ v p.1 p.2) := by
  have hc : ∀ h : X.B.H v, Continuous (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) h) :=
    (Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds v).2.2.1).2.2.2
  have h1 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖⟪X.B.σ v (uMat p.1) (X.B.w v), X.B.σ v (uMat (γ v)) (X.B.σ v (uMat p.2) (X.B.w v))⟫_ℂ‖ₑ) :=
    (((hc _).comp continuous_fst).inner
      ((X.B.σ v (uMat (γ v))).continuous.comp ((hc _).comp continuous_snd))).enorm.measurable
  have h2 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => ‖X.Wloc u v p.1‖ₑ) :=
    ((X.Wloc_cont u v).comp continuous_fst).enorm.measurable
  have h3 : Measurable (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => ‖X.Wloc u' v p.2‖ₑ) :=
    ((X.Wloc_cont u' v).comp continuous_snd).enorm.measurable
  unfold phiV
  exact (h1.mul h2).mul h3

theorem lint_GG_prod (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ∫⁻ y, PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ a, ∫⁻ b, phiV X u u' γ v a b ∂(Formalism.REAL.muG (X.B.I.ε v)) ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm := measurable_phiV X u u' γ
  have h1 : ∀ x : X.B.I.Ginf, ∫⁻ y, PhiGG X.B.σs (X.B.tens X.B.w) (X.Wu u) (X.Wu u') γ x y
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
        ∏ v, ∫⁻ b, phiV X u u' γ v (x v) b ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
    intro x
    simp_rw [phiGG_eq X u u' γ x]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v))
      (fun v b => phiV X u u' γ v (x v) b) (fun v => (hm v).comp measurable_prodMk_left)
  simp_rw [h1]
  exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v))
    (fun v a => ∫⁻ b, phiV X u u' γ v a b ∂(Formalism.REAL.muG (X.B.I.ε v))) (fun v => (hm v).lintegral_prod_right')

end Glob

end Formalism.L2.S.Pv.ConvG
