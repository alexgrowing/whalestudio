import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLawStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharactersStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ) g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · exact GlobalTheory.T.lastStep_localFactor_levelValues_typePrime A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP
  · exact GlobalTheory.T.columnLastStep_localFactor_twist_prime_law A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP

end GlobalTheory.TwTop

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levAt_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU →
    ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi hieq _hAway
  subst hieq
  intro β β' x x' x₁ x₁' κ κ' hx hx' z
  have key : ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' → ∀ Z,
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p₁ p₁' Z) =
        muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (t.m2 + 1 + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p p' Z) := by
    intro p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    have hxi : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' Z =
        _root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' Z := by
      intro q q'
      unfold xiPt
      rw [dif_neg (by omega), if_neg (by omega)]
    have e1 := hxi p₁ p₁'
    have e2 := hxi p p'
    have e3 := GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level A dtU a hPin hTie (t.m2 + 1) hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    simp only [e1, e2, xiTop_eq_prod, e3]
    have hC := hTie.levCpl β
    have hT2 := hTie.levTop β'
    have hLe := hC.1
    have hChi := hC.2.2
    have hLe' := hT2.1
    have hChi' := hT2.2
    have hU := (((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U_eq κ.1).1 κ.2
    have hU' := (((St (t.m2 + 1 + 1) hi).K β').lev.U_eq κ'.1).1 κ'.2
    have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      intro P
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    choose g zz hg using fun P : SB t μ => hLe P _ (hov P) κ.1 hU.1 (hU.2 _)
    choose g' zz' hg' using fun P : SB t μ => hLe' P _ (hov P) κ'.1 hU'.1 (hU'.2 _)
    have c1 := hChi κ g zz hg
    have c2 := hChi' κ' g' zz' hg'
    have hm := GlobalTheory.T.lastStepCharacter_at_levelDet_mul_localCharacters A dtU a hPin hTie hMu hi β β' κ κ' g zz g' zz' hg hg'
    have hprod : (∏ P, zz' P) * (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
        (∏ P, zz P) * ∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [← locAt A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P (g P) (zz P) (g' P) (zz' P)
        (hg P).1 (hg P).2 (hg' P).1 (hg' P).2 Z]
      ring
    have e := congrArg t.seam.σ₀ hprod
    simp only [map_mul] at e ⊢
    have hA : t.seam.σ₀ (∏ P, zz P) ≠ 0 := right_ne_zero_of_mul_eq_one c1
    have hB : t.seam.σ₀ (∏ P, zz' P) ≠ 0 := right_ne_zero_of_mul_eq_one c2
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      (-(((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, zz P) * t.seam.σ₀ (∏ P, zz' P))) * hm +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, zz' P) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))) * c1 +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z)) * e -
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) *
        t.seam.σ₀ (∏ P, zz P)) * c2
  have h₁ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p' :=
    ⟨hEx _ _ β x₁, hEx _ _ β' x₁'⟩
  have h₀ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' :=
    ⟨hEx _ _ β x, hEx _ _ β' x'⟩
  unfold xiAd
  rw [dif_pos h₁, dif_pos h₀]
  exact key _ _ _ _ h₀.1.choose_spec h₀.2.choose_spec h₁.1.choose_spec h₁.2.choose_spec _

end GlobalTheory.TwTop

end
