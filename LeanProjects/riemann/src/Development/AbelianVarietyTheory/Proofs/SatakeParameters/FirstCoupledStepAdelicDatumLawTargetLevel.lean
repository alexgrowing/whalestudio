import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelKeepsBaseCosetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetCoupledEqProdLocalStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplTarget

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem xiCpl1_moved (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {u : Pr.Word} {al : L.β m2} {b : L.β (m2 + 1)}
    (p : ChPt (R := R) sel mu u m2) (p' q' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)) (c : rowSG Pr sel mu → X.Kˣ)
    (hfr : ∀ P, frsF sel mu q' P = frsF sel mu p' P * ((κ P)⁻¹).1)
    (hc : ∀ P, GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ P) (c P)) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hphi : phiT X.K p.deco.1 q'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x) :
    XiCpl1 Ch sel mu cst L m2 al p q' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) =
      ((∏ P, c P : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  unfold XiCpl1
  rw [hphi, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu p P) (frsF sel mu q' P) x = (κ P).1.toLinearMap ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x := by
    rw [hfr]
    refine LinearMap.ext fun w => ?_
    rfl
  have e2 : (frsF sel mu q' P).symm (repY Y) = (κ P).1 ((frsF sel mu p' P).symm (repY Y)) := by
    rw [hfr]
    rfl
  rw [e1, e2]
  exact GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (hc P) (L.h m2 al P) _ _

end Local

set_option maxHeartbeats 1000000 in

theorem levAt_target : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT' _hE hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' hx hp hp' hp₁' w
  subst hi2
  obtain ⟨q', κ'', hq', hphi, hfr, hin⟩ := GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step A dtU a hP hT' hi β' x' x₁' κ' p' hx hp'
  obtain ⟨c, hc, hχ⟩ := GlobalTheory.T.coupledStep_chart_level_at_bad_primes A dtU a hP hT' β' κ' κ'' hin
  have hst := GlobalTheory.T.coupledStepChartLevel_keeps_baseCoset A dtU a hP hT' β' κ' κ'' hin
  have hmu := GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local A dtU a hP hT' hMu β' κ' κ'' hin
  have hAw' := hAw β β' x x₁' x x₁' p q' p p₁' hp hq' hp hp₁' fun v _ => ⟨rfl, rfl⟩
  rw [hAw']
  have law := xiCpl1_moved (Ch := t.Ch) (cst := t.cst μ) hP.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') p p' q' (cosetOf A (t.m2 + 1) hi β' p') κ'' c hfr hc w (hphi p w)
  have hcos : cosetOf A (t.m2 + 1) hi β' q' = cosetOf A (t.m2 + 1) hi β' p' := by
    ext y
    unfold cosetOf y0At
    simp only [Set.mem_setOf_eq, dif_pos rfl]
    refine forall_congr' fun P => ?_
    rw [hfr P]
    exact hst P _
  have ex1 : xiPt A t.m2 hi β β' p q' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p q'
      (cosetOf A (t.m2 + 1) hi β' q') w := by
    unfold xiPt
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  have ex2 : xiPt A t.m2 hi β β' p p' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p p'
      (cosetOf A (t.m2 + 1) hi β' p') w := by
    unfold xiPt
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  rw [ex1, ex2, hcos, hmu, ← hχ, ← map_mul, ← map_mul, mul_comm (∏ P : SB t μ, _), law]

end GlobalTheory.CplTarget
