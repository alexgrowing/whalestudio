import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.GradedForm

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}

def lineGram (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (x : Root m) (y z : CxPts X.str σ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((grD (gramAt E H x.1 y z) x.2 : ℝ) : ℂ)

variable [Finite ι] {E : Fr (ratOf X) m m} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem grD_pos (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) : 0 < grD (gramAt E H x.1 y y) x.2 :=
  ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (h.posDef y _ (E.nonempty (under y)).choose_spec x.1)).2.1 x.2).1

theorem lineGram_smooth (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) :
    SmoothUnitAt (atlas X σ) (lineGram E H x y) y := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (grD_pos h x y).ne')
  · filter_upwards [(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H h y _ (E.nonempty (under y)).choose_spec x.1).2 c hc] with v hv
    intro a b
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v ((GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).2 x.2)

theorem isGramPair_lineGram (h : IsMetricFr E H) (x : Root m) :
    IsGramPair (atlas X σ) (lineGram E H x) (lineGram E H x) := by
  refine ⟨fun y => ⟨lineGram_smooth h x y, lineGram_smooth h x y⟩, fun y => ?_⟩
  have hy := (E.nonempty (under y)).choose_spec
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ hy] with z hyz
  have hz := (E.nonempty (under z)).choose_spec
  set A := (E.nonempty (under y)).choose with hA
  set B := (E.nonempty (under z)).choose with hB
  have hP := (Fr.mem_iff hyz).1 hz
  have hhol := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X _ ((B * A⁻¹) x.1) z (fun i j => mem_O_ratOf.1 ((hP x.1).1 i j)) (hP x.1).2.1
    (mem_O_ratOf.1 (hP x.1).2.2.1)
  have hval : ∀ w : CxPts X.str σ, A ∈ E.S (under w) → B ∈ E.S (under w) →
      Par m ⊤ ((B * A⁻¹).map (ratVal · w)) := fun w h1 h2 => by
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom w
    exact ((Fr.mem_iff h1).1 h2).map_of _ ψ hψ
  let T : CxPts X.str σ → Matrix (Fin 1) (Fin 1) ℂ := fun w _ _ => ratVal ((B * A⁻¹) x.1 x.2 x.2) w
  have hT : HolUnitAt (atlas X σ) T z := by
    refine ⟨?_, fun c hc _ _ => hhol.2 c hc x.2 x.2⟩
    rw [Matrix.det_fin_one]
    have hp := hval z hyz hz x.1
    have hd := hp.2.1
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hp.2.2.2 i j i.2 hij)] at hd
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hd x.2 (Finset.mem_univ _))
  refine ⟨T, T, T, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hyz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hz] with w h1 h2
  rw [and_self]
  have hp := hval w h1 h2 x.1
  have e := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (h.posDef w A h1 x.1) (fun i j hij => hp.2.2.2 i j i.2 hij)
    (isUnit_iff_ne_zero.2 hp.2.1)).2 x.2
  rw [← h.trans w A h1 B h2 x.1] at e
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
  change ((grD (H B w x.1) x.2 : ℝ) : ℂ) = ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2) * ((grD (H A w x.1) x.2 : ℝ) : ℂ) *
    star ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2)
  rw [e, mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem chernFld_lineGram (h : IsMetricFr E H) (x : Root m) :
    chernFld (atlas X σ) (lineGram E H x) 1 = grF E H x := by
  funext p
  have hs := ((lineGram_smooth h x p.pt).2 p.1.1 p.2).self_of_nhds
  have e := GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms _ 1 (fun v => lineGram E H x p.pt (p.ch.symm v))
    (fun _ v => grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2) p.crd hs
    (fun _ => by
      have : p.ch.symm p.crd = p.pt := p.ch.left_inv p.2
      rw [this]; exact grD_pos h x _)
    (Eventually.of_forall fun v => ⟨fun i j hij => absurd (Subsingleton.elim i j) hij.ne, fun _ => rfl⟩) 1
  refine e.trans ?_
  rw [esymm_one, Fin.sum_univ_one, aeval_X]
  rfl

theorem dbarCoh_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  intro F _ σ X ι _ m E H h x
  rw [← chernFld_lineGram h x]
  exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (isGramPair_lineGram h x) 1

end GlobalTheory.ChernCalc.GradedForm
