import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem rename_fockGL_eq_C_mul_colAct : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (u : GLR D n) (P : PolF D m n), ∃ (s : ℂ) (g : {τ : D.host.E →+* ℂ // InPsi H τ} → GL (Fin n) ℂ), MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (fockGL m w 1 u P) = MvPolynomial.C s * GlobalTheory.Harm.colAct ℂ _ Dw.p Dw.q (Fin n) g (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) P) := by
  intro D H Dw m n hΨ hm w a hw u P
  subst hm
  refine ⟨(((detFam w.c u)⁻¹ : ℂˣ) : ℂ), fun t => u ((tauPsi hΨ).symm t), ?_⟩
  have key : (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)).comp (GlobalTheory.ExportSeries.fockSubst (m := Dw.p + Dw.q) w.p u) =
      (GlobalTheory.Harm.colSubst (p := Dw.p) (q := Dw.q) (fun t => (((u ((tauPsi hΨ).symm t))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (fun t => ((u ((tauPsi hΨ).symm t) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).comp
        (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨ρ, i, b⟩ := v
    have hp := (hw ρ).1
    induction i using Fin.addCases with
    | left i =>
      have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_pos hi, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_castAdd]
      erw [GlobalTheory.Harm.colSubst_X_xVar]
      simp [GlobalTheory.Harm.xForm_apply]
    | right j =>
      have hj : ¬ ((Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_neg hj, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_natAdd]
      erw [GlobalTheory.Harm.colSubst_X_yVar]
      simp [GlobalTheory.Harm.yForm_apply]
  have hB : GlobalTheory.ExportSeries.inBasis (1 : GLR D n) u = u := by simp [GlobalTheory.ExportSeries.inBasis]
  rw [GlobalTheory.ExportSeries.fockGL_apply, hB, map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  exact DFunLike.congr_fun key P

end GlobalTheory.FockLetters
