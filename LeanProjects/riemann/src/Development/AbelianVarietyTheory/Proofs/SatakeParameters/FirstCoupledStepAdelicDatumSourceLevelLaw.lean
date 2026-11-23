import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepLevelLocalElementsValuesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValuesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcCpl

section Local
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

open GlobalTheory.TopLaw GlobalTheory.CoupledLaw in

theorem firstCoupledDatum_source_level_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {al : L.β m2}
    {p q : ChPt (R := R) sel mu u m2} (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    {κ : GLQ X.E (R.N m2) (rowSG Pr sel mu)} {c : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = frsF sel mu p P * ((κ P)⁻¹).1)
    (ha : ∀ P, LevAt (L.levG m2 al) (L.levQ m2 al) P (κ P) (c P))
    (hN : q.deco.1.N = p.deco.1.N) (hf : q.deco.1.f = p.deco.1.f) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    XiCpl1 Ch sel mu cst L m2 al q p' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det ((κ P)⁻¹).1 : X.Eˣ) : X.E) =
      (((∏ P, c P)⁻¹ : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  have e0 : phiT X.K q.deco.1 p'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x := by
    unfold phiT Deco.at
    rw [hN, hf]
  unfold XiCpl1
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu p' P) x =
      inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap := by
    rw [hκ]
    rfl
  rw [e1]
  exact psiAt_source hX hPr hL (ha P).inv _ _

end Local
end GlobalTheory.LevSrcCpl

namespace GlobalTheory.LevSrcCpl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem levSrc_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  unfold GlobalTheory.TwV.UnderTie
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie _hEx hMu i hi hi2 hAway β β' x x₁ x' κ p p' p₁ hx hp hp' hp₁ w
  subst hi2
  have hlt : t.m2 < D.R.m := hi
  obtain ⟨g, z, hgz, hchi⟩ := GlobalTheory.T.firstCoupledStep_level_local_elements_values A dtU a hPins hTie hlt β κ
  obtain ⟨q, κP, c, hfr, hlev, hN, hf, hcz, hrho, hin⟩ := GlobalTheory.T.exists_chart_point_frames_moved_by_level A dtU a hPins hTie hlt β κ p g z hgz
  have hq : IsPtAd A a t.m2 hlt.le β x₁ q :=
    GlobalTheory.T.chart_base_point_adelic_right_mul_level A dtU a hPins hTie t.m2 hlt.le β κ x x₁ p q (fun P => ((κP P)⁻¹).1) hx hp hN hf hfr (fun P => ((κP P)⁻¹).2) hin
  have hD := GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues A dtU a hPins hTie hMu hlt β κ g z hgz
  have eA : xiPt A t.m2 hi β β' p₁ p' w = xiPt A t.m2 hi β β' q p' w :=
    congrFun (hAway β β' x₁ x' x₁ x' q p' p₁ p' hq hp' hp₁ hp' (fun _ _ => ⟨rfl, rfl⟩)) w
  rw [eA]
  unfold xiPt
  rw [dif_neg (lt_irrefl _), if_pos rfl, dif_neg (lt_irrefl _), if_pos rfl]
  have hsrc := firstCoupledDatum_source_level_law (G := t.glob) (cst := t.cst μ) (Ch := t.Ch) hPins.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hlt β) p'
    (cosetOf A (t.m2 + 1) hi β' p') hfr hlev hN hf w
  have hprod : ((∏ P, c P : t.X.Kˣ) : t.X.K) * ∏ P, z P = 1 := by
    rw [Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun P _ => hcz P
  simp_rw [hrho] at hsrc
  have e4 := congrArg t.seam.σ₀ hsrc
  have e2 := congrArg t.seam.σ₀ hprod
  have e3 : t.seam.σ₀ (((∏ P, c P)⁻¹ : t.X.Kˣ) : t.X.K) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul] at e4
  rw [map_mul, map_one] at e2
  linear_combination (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * hchi
    - (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      ((((St t.m2 hlt.le).K β).lev.chi κ : ℂˣ) : ℂ)) * e2
    - (t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w)) * hD
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) p p' (cosetOf A (t.m2 + 1) hi β' p') w)) * e3
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * e4

end GlobalTheory.LevSrcCpl
