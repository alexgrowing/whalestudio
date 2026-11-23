import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointMulLevelSameDecorationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixStepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProductStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 1000000 in

theorem levAt_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi him _ β β' x x' x₁ x₁' κ κ' e1 e1' z
  have hm := m_eq t μ
  have hi0 : i < D.R.m := by omega
  have hi1 : i + 1 < D.R.m := by omega
  have H0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  have H1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  unfold xiAd
  rw [dif_pos H0, dif_pos H1]
  have hp := H0.1.choose_spec
  have hp' := H0.2.choose_spec
  have hq := H1.1.choose_spec
  have hq' := H1.2.choose_spec
  generalize H0.1.choose = p at hp ⊢
  generalize H0.2.choose = p' at hp' ⊢
  generalize H1.1.choose = q at hq ⊢
  generalize H1.2.choose = q' at hq' ⊢
  unfold xiPt
  rw [dif_pos him, dif_pos him]
  obtain ⟨k, c, hk, hc, hχ, hd⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie i hi0 him.le β x x₁ κ e1 p q hp hq
  obtain ⟨k', c', hk', hc', hχ', hd'⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie (i + 1) hi1 him β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hN, hf⟩ := GlobalTheory.T.chartPoint_mul_level_same_decoration A dtU a hPin hTie i (Nat.le_of_succ_le hi) β x x₁ κ e1 p q hp hq
  obtain ⟨hN', hf'⟩ := GlobalTheory.T.chartPoint_mul_level_same_decoration A dtU a hPin hTie (i + 1) hi β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hmu, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 i (Nat.le_of_succ_le hi) β κ _ hd
  obtain ⟨-, hmu'⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 (i + 1) hi β' κ' _ hd'
  have core : ∀ W, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W) := by
    intro W
    have e0 : phiT t.X.K q.deco.1 q'.deco.1 W = phiT t.X.K p.deco.1 p'.deco.1 W := by
      unfold phiT
      refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
      simp only [Deco.at, hN, hN', hf, hf']
    have law := GlobalTheory.MatLaw.xiEntry_law hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) him
      (γ := 1) (γ' := 1) (p := p) (q := q) (p' := p') (q' := q') (κ := k) (κ' := k') (a := c) (a' := c')
      (fun P => by rw [hk P, OneMemClass.coe_one, one_mul]) (fun P => by rw [hk' P, OneMemClass.coe_one, one_mul]) hc hc' W
      (by exact e0)
    have hW : ((1 : UF t.X.E (D.R.N (i + 1))).1.toLinearMap ∘ₗ W ∘ₗ (1 : UF t.X.E (D.R.N i)).1.symm.toLinearMap) = W :=
      LinearMap.ext fun v => rfl
    rw [hW, Finset.prod_mul_distrib] at law
    have law' := congrArg t.seam.σ₀ law
    simp only [map_mul, Units.val_mul, Pi.inv_apply] at law'
    have hCC : t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ ((((∏ P, c P)⁻¹ : t.X.Kˣ)) : t.X.K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    linear_combination (-(t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W))) * hmu
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K)) * law'
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c' P : t.X.Kˣ)) : t.X.K) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hCC
      + (((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hmu'
      + (t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hχ
      - (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hχ'
  exact core _

end GlobalTheory.TwV

end
