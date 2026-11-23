import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem ratVal_zero_var {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (y : CxPts X.str σ) :
    ratVal (0 : X.Fn) y = 0 := by
  have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial (0 : Γ(X.X, ⊤))
  rw [map_zero, ev_eq mem_ptsIn_top, map_zero] at e
  exact e

theorem isGramPair_ldPart (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H) (τ : ι) :
    IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  have hA : ∀ y : CxPts X.str σ, (E.nonempty (under y)).choose ∈ E.S (under y) :=
    fun y => (E.nonempty (under y)).choose_spec
  have hsm := fun y => GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH y _ (hA y) τ
  have hT : ∀ (A B : Mat m X.Fn) (w : CxPts X.str σ), A ∈ E.S (under w) → B ∈ E.S (under w) →
      HolUnitAt (atlas X σ) (fun z => ((B * A⁻¹) τ).map (ratVal · z)) w ∧
      ∀ i j : Fin (m τ), i < j → ((B * A⁻¹) τ).map (ratVal · w) i j = 0 := by
    intro A B w hAw hBw
    have hp := ((Fr.mem_iff hAw).1 hBw) τ
    refine ⟨GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) ((B * A⁻¹) τ) w (fun i j => mem_O_ratOf.1 (hp.1 i j)) hp.2.1
      (mem_O_ratOf.1 hp.2.2.1), fun i j hij => ?_⟩
    rw [Matrix.map_apply, hp.2.2.2 i j i.2 hij]
    exact ratVal_zero_var w
  refine ⟨fun y => ⟨(hsm y).1, ?_⟩, fun y => ?_⟩
  · refine ⟨(GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (hH.posDef y _ (hA y) τ)).2.2.2, fun c hc => ?_⟩
    filter_upwards [(hsm y).2 c hc] with v hv
    exact (GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).1
  · have h1 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ (hA y)
    filter_upwards [h1, h1.eventually_nhds] with z hz hz'
    have h2 := GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ (hA z)
    obtain ⟨hol, tri⟩ := hT _ _ z hz (hA z)
    refine ⟨_, _, fun w => Matrix.diagonal fun i =>
      (((E.nonempty (under z)).choose * (E.nonempty (under y)).choose⁻¹) τ).map (ratVal · w) i i,
      hol, hol, ⟨?_, fun c hc a b => ?_⟩, ?_⟩
    · rw [Matrix.det_diagonal, ← Matrix.det_of_lowerTriangular _ (fun i j hij => tri i j hij)]
      exact hol.1
    · by_cases hab : a = b
      · subst hab
        filter_upwards [hol.2 c hc a a] with v hv
        simpa only [Matrix.diagonal_apply_eq] using hv
      · exact Eventually.of_forall fun v => by
          simp only [Matrix.diagonal_apply_ne _ hab]
          exact differentiableAt_const _
    · filter_upwards [hz', h2] with w hwA hwB
      obtain ⟨holw, triw⟩ := hT _ _ w hwA hwB
      have e := hH.trans w _ hwA _ hwB τ
      change gramAt E H τ z w = _ * gramAt E H τ y w * _ at e
      refine ⟨e, ?_⟩
      rw [e]
      exact (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (hH.posDef w _ hwA τ) triw holw.1).1

end GlobalTheory.ChernCalc
