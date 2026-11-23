import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBoundStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopFibre

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_comp_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h

set_option backward.isDefEq.respectTransparency false in

theorem stalkSpecializes_comp_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_comp_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (ψ : R →+* R') {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z)) :
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_comp_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_comp_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_comp_stalkClosedPointTo ψ z)

theorem coordsAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q) {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} {L L' : Type} [Field L] [Field L'] (ψ : L →+* L') {z : Spec (CommRingCat.of L) ⟶ X}
    {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (Spec.map (CommRingCat.ofHom ψ) ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_comp ψ hr (hall _), by simp only [e, map_mul]⟩

end Values

theorem logBound_mono {C C' t : ℝ} (h0 : 0 ≤ C) (h : C ≤ C') (ht : 0 ≤ t) :
    C * Real.log (2 + C + t) + C ≤ C' * Real.log (2 + C' + t) + C' := by
  have h1 : 0 ≤ Real.log (2 + C + t) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 + C + t) ≤ Real.log (2 + C' + t) := Real.log_le_log (by linarith) (by linarith)
  have h3 := mul_le_mul h h2 h1 (h0.trans h)
  linarith

theorem fibreInput : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  intro h1 h2 h3 h4 h5 E _ _ _ H D l Xo c Y S _ R 𝔐 Fl e hpq hroot
  obtain ⟨h, horth⟩ := GlobalTheory.T.exists_orthogonal_lie_metric E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐
  obtain ⟨C₁, hC₁, hslope⟩ := GlobalTheory.T.hodge_cpt_lie_metric_bound h1 h2 h3 h4 h5 E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 h hpq
  have hdeg : (fun r => (R.x 1 r).a) = R.xdeg := funext fun r => R.x_deg 1 r
  obtain ⟨C₂, hht⟩ := GlobalTheory.T.flag_line_degree_formula E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h (R.x 1) e (R.x_smooth 1)
    (hdeg.symm ▸ hroot)
  have hch : CharZero R.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun L _ _ w hw => ?_⟩
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.number_field_point_integral_model 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ hch 𝔐.all 𝔐.tie L w hw
  obtain ⟨L', _, _, ε, hs⟩ := hslope L z₀
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨B, MB, hB⟩ := GlobalTheory.T.lie_metric_hermitian_bundle 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M h L'
    (spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
  obtain ⟨A, hA, hW⟩ := GlobalTheory.T.orthogonal_metric_flag_degree E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h horth L' _ B MB hB
  have hpt : spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀ =
      spMap ε ≫ spMap (algebraMap (𝓞 L) L) ≫ z₀ := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hz : CoordsAt 𝔐.ξ R.y (spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
      fun p => ε (w p) := by
    rw [hpt]
    exact coordsAt_comp 𝔐.all ε hz₀
  have hext : ∀ r, Ht.lineHt (R.x 1 r) L' (fun p => ε (w p)) = Ht.lineHt (R.x 1 r) L w := fun r => by
    simpa using GlobalTheory.T.line_height_invariant_scaling R.K R.ι (R.x 1 r) L L' ε w (fun _ => 1) hw.1 fun _ => one_ne_zero
  obtain ⟨ha, hb⟩ := hht L' _ _ hz B MB A hB hW
  refine ⟨L', inferInstance, inferInstance, ε, B, A, hA, fun τ i => ?_, fun τ i => ?_, ?_⟩
  · rw [← hext]
    exact (ha τ i).trans (le_max_right _ _)
  · rw [← hext]
    exact (hb τ i).trans (le_max_right _ _)
  · exact (hs B MB hB).trans
      (EReal.coe_le_coe_iff.2 (logBound_mono hC₁ (le_max_left _ _) (le_max_right _ _)))

end GlobalTheory.CompanionTheory.Ar.TopFibre
