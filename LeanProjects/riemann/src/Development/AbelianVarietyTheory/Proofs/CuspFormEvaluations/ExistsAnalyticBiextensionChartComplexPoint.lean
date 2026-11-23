import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivialStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChartStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnEStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbertStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReadingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJetsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSectionStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivialStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSecondPartialLawTrivialStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivialStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem isFrame_of_isAnE (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) :
    IsFrame y g Φ.jx (anFB ty).G.F (anFB ty).A.act (anFB ty).ph1 (anFB ty).ph2 (anFB ty).sy (anFB ty).ad e := by
  have hI := GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ
  exact ⟨fun m => (he m).1, GlobalTheory.T.analyticFrame_first_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_second_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he, GlobalTheory.T.analyticFrame_symmetry_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_adjointness_series_trivial E H Dw l Xo c y g ty el Φ hI hst e he⟩

theorem isGerm_tay_of_rd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (wP : PrimTy H Xo) (hw : IsPrim wP) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ)
    (hF : Φ.toAnFr.Rd k F θ) : IsGerm y g Φ.jx (anFB ty).A.act e wP k F (tay θ 0) := by
  simp only [IsGerm]
  intro m
  have hJ : Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) :=
    (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  obtain ⟨τ, -, hτ⟩ := GlobalTheory.T.exists_generator_jet_reading _ _ _ _ _ Φ.toAnFr 1 m (Fin 1) (fun _ => (Φ.jx m).left) (fun _ => (k : ℤ))
    (fun _ => LinearMap.proj 0) (fun _ => hJ)
  obtain ⟨F', hpull, hval⟩ := GlobalTheory.T.isValueAt_jetPoint_cmFrame_section E H Dw l Xo c y g ty el Φ m k F θ τ hF hτ
  have hc := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).1 m k τ hτ
  exact ⟨F', τ, hpull, hc, hval⟩

noncomputable def AnPt.chartOf (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e)
    (wP : PrimTy H Xo) (hw : IsPrim wP) : ChartAt Xo c y where
  d := g
  B := anFB ty
  uvec := anUvec el
  x := Φ.jx
  e := e
  wP := wP
  h := 0
  chart := GlobalTheory.T.cmFrame_exponential_jets_isChart E H Dw l Xo c y g ty el Φ
  frame := isFrame_of_isAnE Φ hst e he
  prim := hw
  gauge := anFB_canon ty
  rig0 := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).2

end

theorem rename_cast_refl {g : ℕ} (f : MvPowerSeries (Fin 1 × Fin g) ℂ) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) f = f := by
  have h : (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) = id := funext fun p => rfl
  rw [h]
  exact MvPowerSeries.rename_id_apply f

theorem exists_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hst
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_analyticFrame_jetPair_isAnE E H Dw l Xo c y g ty el Φ
  obtain ⟨wP, hw⟩ := (GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ).1
  refine ⟨AnPt.chartOf Φ hst e he wP hw, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    first
      | rfl
      | simp [AnPt.chartOf, anFB, Germ.FB.triv, addFGLaw]
  · intro ℓ i'
    first
      | rfl
      | simp [AnPt.chartOf, anUvec, Pi.single_apply, eq_comm]
      | (simp only [AnPt.chartOf, anUvec]; done)
  · intro k F θ hF
    show IsGerm y g Φ.jx (anFB ty).A.act e wP k F
      (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) (tay θ 0))
    rw [rename_cast_refl]
    exact isGerm_tay_of_rd Φ e he wP hw k F θ hF

end GlobalTheory.AnVal
