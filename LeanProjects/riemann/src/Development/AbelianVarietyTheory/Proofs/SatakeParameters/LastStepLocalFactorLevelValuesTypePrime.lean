import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrimeStatement

noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hC hF hT hF' Z
  have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
  have hDt : topDep t.sel (t.tup μ) (t.cst μ) P = 1 := by unfold topDep; simp [hP]
  obtain ⟨Gg, rfl, hsrc⟩ := GlobalTheory.T.last_step_local_factor_source_law_coupled_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) _ P hP g z hC.1
  obtain ⟨Gt, rfl, htgt⟩ := GlobalTheory.T.last_step_local_factor_target_law_top_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) P hP g' z' hT
  obtain ⟨k, hk, hkr⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ hx p p₁ hp hp₁ P hP (t.cst μ).D hD Gg hF
  obtain ⟨k', hk', hkr'⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ' hx' p' p₁' hp' hp₁' P hP _ hDt Gt hF'
  obtain ⟨i0, i1, hdiff⟩ := GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime A dtU a hPin hTie (Nat.le_of_succ_le hi) β p p₁ P hP Gg k z hC hkr hk
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsG t.sel (t.tup μ) p₁' P) Z =
      (k'⁻¹).1.toLinearMap ∘ₗ (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) := by
    rw [frsG_eq, frsG_eq, hk, hk']
    rfl
  have hs := hsrc k hkr (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z) _ _ i0 hdiff
  have ht := htgt k' hkr' (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) _ i1
  unfold topF
  rw [e1]
  linear_combination rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det Gg.1 : t.X.Eˣ) : t.X.E) * ht + hs

end GlobalTheory.TwTop

end
