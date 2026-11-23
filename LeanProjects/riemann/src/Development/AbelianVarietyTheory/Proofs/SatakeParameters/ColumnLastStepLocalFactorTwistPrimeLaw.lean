import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwTopQ

theorem topF_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
  topF Ch sel mu cst i P p Y p' x = topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem locq_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hcpl hfr htop hfr' Z
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hD := hok.depthQ P hP
  have hM := hc.M_pos
  have hX : t.X.Ok := hPin.fields.ok
  have hU := qUnif_of t.sel (t.tup μ) hX t.pr_ok hPin.sel
  have hgI : g ∈ GLint t.X.E _ P.1 :=
    hok.int (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β) P ((exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hcpl.1⟩)
  have hg'I : g' ∈ GLint t.X.E _ P.1 := GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime _ _ _ _ _ P hP g' z' htop
  have hdep : topDep t.sel (t.tup μ) (t.cst μ) P = 2 * (t.cst μ).M := if_neg hP
  obtain ⟨hk, hkc⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ.1 p p₁ hx hp hp₁ P (t.cst μ).D g
    (hc.D_pos P) le_rfl hgI hfr
  obtain ⟨hk', hkc'⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ'.1 p' p₁' hx' hp' hp₁' P
    (topDep t.sel (t.tup μ) (t.cst μ)) g' (by rw [hdep]; omega) (by rw [hdep]; exact hD) hg'I hfr'
  rw [hdep] at hkc'
  have hy0 : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
    unfold y0At
    rw [dif_pos rfl]
  obtain ⟨hW0, hV1, hW⟩ := GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime A dtU a hPin hTie (Nat.le_of_succ_le hi) β P hP p p₁ g
    ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)) hgI (by rw [hy0]; exact hcpl.2) hk hkc
    (fun w => by simp)
  rw [topF_eq, topF_eq]
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p₁' P) Z =
      ((frsF t.sel (t.tup μ) p₁' P).trans ((frsF t.sel (t.tup μ) p' P).symm.trans g'.symm)).symm.toLinearMap ∘ₗ
        (g'.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) Z ∘ₗ g.toLinearMap) ∘ₗ
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp [inFr, LinearEquiv.trans_symm]
  have e2 : (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)) =
      ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).symm
        (g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)))) := by
    simp [LinearEquiv.trans_symm]
  have hy'' : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).M) *
      g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) l) := by
    have h1 := (hk _).2 hV1
    rw [map_smul] at h1
    have e3 : ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm))
        ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) =
        g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) := by
      simp
    rw [e3] at h1
    intro l
    simpa using (ciMem_stdAt _ _).1 h1 l
  rw [e1, e2, GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime t.Ch t.sel (t.tup μ) (t.cst μ) (m_eq t μ) hc P hP hD _ _ hk hkc hk' hkc' _ _ hy'']
  exact GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) hok hU (A.ib (t.m2 + 1) (cpl_lt t μ) β) P hP g z hcpl.1 g' z' htop _ _ _ hW hW0

end GlobalTheory.TwTopQ
