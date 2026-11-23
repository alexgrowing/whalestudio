import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtChaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeMetricBoundedDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifDens

open Filter Topology GlobalTheory.UnifDens in

theorem chernTopPart_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ A hAD hAm hinj
  have hdim := GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hcont, hana⟩ := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have h3a := GlobalTheory.T.point_class_density_uniformisation_chart_change E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  have h3b := GlobalTheory.T.pointClassDensity_hodgeMetric_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  set D := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hDdef
  have hDo : IsOpen D := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set L := flatL hdim with hLdef
  set C : ℝ := grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef, grassConst]
    refine pow_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity)) _
  set dens : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → ℝ := fun w =>
    ∏ i, ((hQ (unflat w i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) with hdens
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set ρ : AlgChart X.str (σ.comp e.toRingHom) X.dim → CxPts X.str (σ.comp e.toRingHom) → ENNReal := fun ch y =>
    ENNReal.ofReal ((((1 : ℤˣ) : ℤ) : ℝ) * chernTop (pointPoly H Dw)
      (fun v => lieGram e U hj f₀ A₀ (Eb.nonempty (under y)).choose (ch.e.symm v)) (ch.e y)) with hρ
  have hμ : chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 =
      glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ := rfl
  have hpre : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (D ∩ ψ ⁻¹' S) := by
    intro S hS
    have hm : Measurable (D.restrict ψ) := (continuousOn_iff_continuous_restrict.1 hcont).measurable
    have := hDo.measurableSet.subtype_image (hm hS)
    convert this using 1
    ext w
    constructor
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hw⟩, hwS, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwS, rfl⟩
      exact ⟨hw, hwS⟩
  have key : ∀ (ch : AlgChart X.str (σ.comp e.toRingHom) X.dim)
      (B : Set ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ)), MeasurableSet B → B ⊆ D → Set.InjOn ψ B →
      chartMeas ch.e (ρ ch) (ψ '' B) = ENNReal.ofReal C * μD (B ∩ ψ ⁻¹' ch.e.source) := by
    intro ch B hB hBD hBi
    set B' := B ∩ ψ ⁻¹' ch.e.source with hB'
    have hB'm : MeasurableSet B' := by
      have e0 : B' = B ∩ (D ∩ ψ ⁻¹' ch.e.source) := by
        ext w
        simp only [hB', Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, hBD h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      rw [e0]
      exact hB.inter (hcont.isOpen_inter_preimage hDo ch.e.open_source).measurableSet
    have hψB : MeasurableSet (ψ '' B) := hB.image_of_continuousOn_injOn (hcont.mono hBD) hBi
    rw [chartMeas_apply ch.e (ρ ch) hψB]
    have e1 : ch.e.source ∩ ψ '' B = ψ '' B' := by
      rw [hB', Set.image_inter_preimage, Set.inter_comm]
    set φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (L u)) with hφ
    set S := L ⁻¹' B' with hS
    have e2 : ch.e '' (ψ '' B') = φ '' S := by
      rw [hS, hφ, ← Set.image_image (fun w => ch.e (ψ w)) L, Set.image_preimage_eq _ L.surjective,
        Set.image_image]
    have hSm : MeasurableSet S := L.continuous.measurable hB'm
    have hdiff : ∀ u ∈ S, DifferentiableAt ℂ φ u := by
      intro u hu
      have hu' : L u ∈ B' := hu
      exact (hana (L u) (hBD hu'.1) ch hu'.2).differentiableAt.comp u L.differentiableAt
    have hder : ∀ u ∈ S, HasFDerivWithinAt φ ((fderiv ℂ φ u).restrictScalars ℝ) S u :=
      fun u hu => ((hdiff u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjφ : Set.InjOn φ S := by
      intro u1 h1 u2 h2 h12
      have h1' : L u1 ∈ B' := h1
      have h2' : L u2 ∈ B' := h2
      have h3 : ψ (L u1) = ψ (L u2) := ch.e.injOn h1'.2 h2'.2 h12
      exact L.injective (hBi h1'.1 h2'.1 h3)
    rw [e1, e2, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinjφ]
    have hint : ∀ u ∈ S, ENNReal.ofReal |((fderiv ℂ φ u).restrictScalars ℝ).det| * ρ ch (ch.e.symm (φ u)) =
        ENNReal.ofReal (C * dens (L u)) := by
      intro u hu
      have hu' : L u ∈ B' := hu
      have hsym : ch.e.symm (φ u) = ψ (L u) := ch.e.left_inv hu'.2
      rw [hsym]
      have hdet : ((fderiv ℂ φ u).restrictScalars ℝ).det =
          Complex.normSq (LinearMap.det (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) := by
        have := LinearMap.det_restrictScalars (R := ℝ)
          (f := (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim))
        rw [Algebra.norm_complex_apply] at this
        exact this
      have hA := (Eb.nonempty (under (ψ (L u)))).choose_spec
      have ha := h3a u (hBD hu'.1) ch hu'.2 _ hA
      have hb := h3b u (hBD hu'.1) _ hA
      rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _), hρ, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
      congr 1
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [← ha, hb]
    rw [setLIntegral_congr_fun hSm hint]
    have hmp := (flatL_mp hdim).setLIntegral_comp_preimage_emb L.toHomeomorph.measurableEmbedding
      (fun w => ENNReal.ofReal (C * dens w)) B'
    rw [hS]
    refine hmp.trans ?_
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hμD, muD, withDensity_apply _ hB'm,
      Measure.restrict_restrict hB'm, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBD)]

  set ν : Measure (CxPts X.str (σ.comp e.toRingHom)) := ENNReal.ofReal C • Measure.map ψ (μD.restrict A) with hν
  have hae : AEMeasurable ψ (μD.restrict A) := (hcont.mono hAD).aemeasurable hAm
  have hνT : ∀ S, MeasurableSet S → ν S = ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.smul_apply, Measure.map_apply_of_aemeasurable hae hS, Measure.restrict_apply' hAm,
      Set.inter_comm, smul_eq_mul]
  have hAS : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (A ∩ ψ ⁻¹' S) := by
    intro S hS
    have e0 : A ∩ ψ ⁻¹' S = A ∩ (D ∩ ψ ⁻¹' S) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨h.1, hAD h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e0]
    exact hAm.inter (hpre S hS)
  have hψA : MeasurableSet (ψ '' A) := hAm.image_of_continuousOn_injOn (hcont.mono hAD) hinj
  have hle : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) ≤ ν := by
    rw [glueMeas, GlobalTheory.ChernScale.restrict_iSup_eq _ hψA]
    refine iSup_le fun ch => Measure.le_iff.2 fun S hS => ?_
    rw [Measure.restrict_apply hS, hνT S hS, Set.inter_comm, ← Set.image_inter_preimage,
      key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left)]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have heq : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) = ν := by
    refine ext_of_cover (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e.source)
      (fun ch => ch.e.open_source) (fun y => AlgChart.exists_mem_source y) fun ch S hS hSc =>
        le_antisymm (Measure.le_iff'.1 hle S) ?_
    rw [Measure.restrict_apply hS, hνT S hS]
    have e3 : A ∩ ψ ⁻¹' S = (A ∩ ψ ⁻¹' S) ∩ ψ ⁻¹' ch.e.source :=
      (Set.inter_eq_left.2 fun w (hw : w ∈ A ∩ ψ ⁻¹' S) => hSc hw.2).symm
    calc ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S)
        = chartMeas ch.e (ρ ch) (ψ '' (A ∩ ψ ⁻¹' S)) := by
          rw [key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left), ← e3]
      _ = chartMeas ch.e (ρ ch) (S ∩ ψ '' A) := by rw [Set.image_inter_preimage, Set.inter_comm]
      _ ≤ glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ (S ∩ ψ '' A) :=
          Measure.le_iff'.1 (le_iSup (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => chartMeas ch.e (ρ ch)) ch) _
  rw [hμ, ← Measure.restrict_apply_self, heq, hνT _ hψA, Set.inter_eq_left.2 (Set.subset_preimage_image ψ A)]

end GlobalTheory.UnifDens
