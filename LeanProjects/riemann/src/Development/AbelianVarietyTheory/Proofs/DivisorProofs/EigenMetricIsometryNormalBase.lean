import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqGenericPointOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleRankComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGenericFibreIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfVarietyComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAssignmentMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricComparisonNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCovDeg

open GlobalTheory.FlagCov GlobalTheory.PairCov GlobalTheory.FlagCovDivCore

theorem flagMat_of_pull {B Y X : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B) (ρ : X ⟶ Y)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f)
    {K : Type} [CommRing K] (z : Sp K ⟶ X) (A : Matrix (Fin r) (Fin r) K)
    (h : FlagMat (hM.pullback π) ρ (fl.pull ρ) (haveI := hM.isQuasicoherent; hf.pullback π) z A) :
    FlagMat hM π fl hf (z ≫ ρ) A := by
  haveI := hM.isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  refine ⟨h.1, fun k W hWV t hy => ?_⟩
  obtain ⟨cf, h1, h2⟩ := h.2 k (ρ ⁻¹ᵁ W) (ρ.preimage_mono hWV) (QCoh.pullbackSections ρ (fl.F k) le_rfl t) hy
  refine ⟨cf, h1, Eq.trans (funext fun b => ?_) h2⟩
  have e := QCoh.pullback_map_app_pullbackSections ρ (fl.ι k) (le_refl (ρ ⁻¹ᵁ W)) t
  have e' := (hf.pullback π).pullback_basis_repr ρ hWV (le_refl (ρ ⁻¹ᵁ W)) ((fl.ι k).app W t) b
  rw [← e] at e'
  exact ((congrArg (TangentOrigin.evalPt z (ρ ⁻¹ᵁ W) hy) e').trans (GlobalTheory.FlagSec.evalPt_appLE ρ z W _ le_rfl hy hy _)).symm

variable {D : D7} {O : Setup D} {c : O.s.Comp}

theorem agreeAt_of_isFrameSecX {B Bg Y X G : Scheme.{0}} [IsIntegral G] (σ : D.host.E →+* ℂ) {M : B.Modules}
    (hM : IsVB M (O.S.Dw.mult σ)) {jB : Bg ⟶ B} {πB : Bg ⟶ gen O.s.T.Z} {t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB}
    (hLF : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t) {π : Y ⟶ B} {ρ : X ⟶ Y}
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) (O.S.Dw.mult σ)) {j : G ⟶ X}
    {φ : (O.var c).Fn →+* G.functionField} {jG : G ⟶ Bg} (hjG : jG ≫ jB = j ≫ ρ ≫ π)
    {χ : O.κ.c.F →+* G.functionField} (hχ : (genPt G ≫ jG) ≫ πB ≫ genStr O.s.T.Z = spMap χ)
    (g : EigFrame O.s.T.Z χ ((genPt G ≫ jG) ≫ πB ≫ genι O.s.T.Z)) (hg : (O.Φ.C c).f0.IsMap φ g)
    (h : ∀ i, ∃ r, IsFrameSecX σ hM jB πB t π ρ (fl.pull ρ) j φ jG i r) :
    AgreeAt O.s.T.Z hM jB t π fl false (genPt G ≫ j ≫ ρ) (genPt G ≫ jG) ((genPt G ≫ jG) ≫ πB ≫ genι O.s.T.Z) (g.v σ) := by
  intro V f hf hx d hd
  haveI := hM.isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  choose r h using h
  let y := (genPt G ≫ j) (IsLocalRing.closedPoint G.functionField)
  obtain ⟨cc, hcc⟩ : ∃ cc : ∀ k, (((fl.pull ρ).root k).pull j).ι, ∀ k, y ∈ (cc k PUnit.unit).U := by
    choose U e hU he using fun k => (fl.pull ρ).isVB_gr k y
    exact ⟨fun k _ => ⟨U k, e k, he k⟩, hU⟩
  have hV : y ∈ ρ ⁻¹ᵁ (π ⁻¹ᵁ V) := by
    have := hx (x := IsLocalRing.closedPoint G.functionField) trivial
    rw [Category.assoc, hjG] at this
    exact this
  obtain ⟨W, hWV, hW, s, hxW, hs, hfr⟩ := exists_lifts_isFrame (fl.pull ρ) (fun k => cc k PUnit.unit) hcc hV
  have hsp := GlobalTheory.FlagCovQF.spans_of_lifts (fl.pull ρ) s fun k => by
    have := (cc k PUnit.unit).isFrame.res (hW k)
    rw [hs]
    convert this using 3 with i
    exact congrArg _ (Subsingleton.elim _ _)
  have hKW : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W := fun p _ => by
    obtain rfl : p = IsLocalRing.closedPoint G.functionField := Subsingleton.elim (α := PrimeSpectrum G.functionField) _ _
    exact hxW
  have hA := flagMat_of_pull hM π ρ fl hf _ _ (AdaptMat.flagMat_of_adapted _ _ _ _ (hM.pullback π) ρ (fl.pull ρ) _ _
    (hf.pullback π) _ (genPt G ≫ j) W hWV hKW _ ⟨hfr, hsp⟩)
  choose w cf h1 h2 h3 h4 using fun k => h k (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hx
  have hu := hLF.1 V f hf _ (genPt G ≫ jG) hx (χ.comp O.κ.e.toRingHom) (by
    rw [spMap_trans, ← hχ]; simp only [Category.assoc])
  rw [show (χ.comp O.κ.e.toRingHom).comp O.κ.e.symm.toRingHom = χ from RingHom.ext fun a => by simp] at hu
  obtain ⟨u, hu⟩ := exists_frame_of_basis g hu
  have hco : u.co g σ = d.transpose := EigFrame.co_eq fun i => by rw [hu]; exact hd i
  have hC : (Matrix.of cf).BlockTriangular OrderDual.toDual := fun a b hab => h4 a b hab
  have hCu : IsUnit (Matrix.of cf).det := by
    rw [Matrix.det_of_isLowerTriangular _ hC]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => (h3 i).trans_ne (Units.ne_zero _)).isUnit
  have := (Matrix.of cf).invertibleOfIsUnitDet hCu
  have hA' := hA.mul (T := (Matrix.of cf)⁻¹) (Matrix.isUnit_nonsing_inv_det _ hCu)
    fun a b hab => Matrix.blockTriangular_inv_of_blockTriangular hC hab
  rw [Category.assoc] at hA'
  convert hA' using 1
  rw [eq_comm, Matrix.inv_mul_eq_iff_eq_mul_of_invertible]
  ext a b
  have e := co_mulVec u u g σ (w := w a) (by rw [hu, Category.assoc]; exact h1 a)
    (by rw [funext (hg σ), Category.assoc]; exact h2 a)
  rw [EigFrame.co_self, Matrix.one_mulVec, hco, Matrix.mulVec_transpose] at e
  exact congrFun e b

set_option maxHeartbeats 1000000 in

theorem pairCoverDeg : Hypotheses2 → HypothesesH → RegularAlteration → ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (M : DRBase O c) (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)) (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf) (u : ∀ σ, E σ ⟶ E' σ), IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → (∀ σ, IsoHom (h σ) (h' σ) (u σ)) → ∀ (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB) (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB), PairAt O R c q E E' h h' u jB πB t t' (fun σ' => M.x.eigMetAt σ' (some R)) → ∀ (β : B ⟶ M.B) (w : β ≫ strL M = q), jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z → β (genericPoint B) = genericPoint M.B → PairCoverDeg O R c q E E' H H' u (β.residueDegree (genericPoint B)) := by
  intro p2 pH pRA D O hO R hR c M B _ q E E' h h' H H' u hq hn hu Bg jB πB t t' hW β _ hβ _
  let G : ∀ σ', EigMet O.s.T.Z σ' := fun σ' => M.x.eigMetAt σ' (some R)
  replace hW : PairWit O R c q E E' h h' u jB πB t t' G := hW
  obtain ⟨pbB, finB, -, frE, frE', hmat, latE, latE', -, metE, metE'⟩ := id hW
  obtain ⟨Y, iY, π, fl, hfb, arY, nY⟩ := GlobalTheory.T.exists_normal_isFlagBundle_isArithVar (𝓞 D.what₂.LL) B q _ hq hn (D.host.E →+* ℂ) E O.S.Dw.mult
    (fun σ => (h σ).isVB)
  have arY' : IsArithVar (π ≫ q) (O.var c).dim := by
    rw [← GlobalTheory.T.dimension_of_variety_component D O hO c]
    exact arY
  obtain ⟨Gs, jY, s, pbY, iG⟩ : ∃ (Gs : Scheme.{0}) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp D.what₂.LL),
      IsPullback jY s (π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧ IsIntegral Gs :=
    ⟨_, _, _, GlobalTheory.FlagGenFib.isPullback_f q π, GlobalTheory.FlagGenFib.isIntegral_Gf q π _ arY'⟩
  obtain ⟨X, iX, ρ, fl', j, ej, pbX, hcov, nX, hcomp⟩ := GlobalTheory.T.flag_pullback_generic_fibre D.what₂.LL Y (π ≫ q) _ arY' nY (D.host.E →+* ℂ)
    (fun σ => (Scheme.Modules.pullback π).obj (E σ)) (fun σ => (Scheme.Modules.pullback π).obj (E' σ)) O.S.Dw.mult
    (fun σ => (h' σ).isVB.pullback π) (fun σ => (Scheme.Modules.pullback π).map (u σ)) fl Gs jY s pbY
    (fun σ => GlobalTheory.T.frame_assignment_morphism D O B q Bg jB πB pbB σ (E σ) (E' σ) (h σ).isVB (h' σ).isVB (u σ) (t σ) (t' σ) (frE σ) (frE' σ)
      (hmat σ) Y Gs π jY s pbY.w)
  obtain ⟨πG, φ, jG, r, hcc, hr⟩ := GlobalTheory.T.eigen_metric_comparison_normal p2 pH pRA D O hO R hR c B q E E' h h' u hq hn hu Bg jB πB t t' G hW
    Y π fl hfb arY' nY X Gs ρ j s (ej ▸ pbY) pbX
  choose r' hr' using fun σ => GlobalTheory.T.pair_cover_compatibility D O R c B q Bg jB πB G Y X Gs π ρ j πG φ jG hcc σ (E σ) (E' σ) (h σ).isVB
    (h' σ).isVB (u σ) (t σ) (t' σ) (frE σ) (frE' σ) (hmat σ) ((fl σ).pull ρ) (fl' σ) (hcomp σ) (r σ) (hr σ)
  obtain ⟨-, -, -, -, pb, hfin, hsur, φs, c1, c2⟩ := id hcc
  let V : Cover (O.var c) :=
    { X := X, p := ρ ≫ π ≫ q, ar := hcov.1, normal := nX, G := Gs, j := j, π := πG, pb := pb, fin := hfin,
      surj := hsur, φ := φ, φ_spec := φs }
  refine ⟨V, Y, iY, π, ρ, rfl, fl, fl', ?_, arY', hcov, hfb, hcomp, fun z => ?_, fun k z hk => ?_⟩
  · have hφ : genPt Gs ≫ πG = spMap φ ≫ genericPt (O.var c) := φs
    have e (T : Scheme.{0}) (a : gen O.s.T.Z ⟶ T) :
        (genPt Gs ≫ jG) ≫ πB ≫ a = spMap φ ≫ (genericPt (O.var c) ≫ (O.Φ.C c).π) ≫ a := by
      rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc, ← Category.assoc, hφ]
      simp only [Category.assoc]
    have hχ : (genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z = spMap (φ.comp (constF O.κ.e (O.var c))) := by
      rw [e, GlobalTheory.ShFam.TieBase.genericPt_str O.κ.e (O.var c) (O.Φ.C c).π (O.Φ.C c).π_str]
      exact (Spec.map_comp _ _).symm
    have hx : (genPt Gs ≫ jG) ≫ πB ≫ genι O.s.T.Z = spMap φ ≫ genericPt (O.var c) ≫ (O.Φ.C c).π ≫ genι O.s.T.Z :=
      (e _ _).trans (congrArg _ (Category.assoc _ _ _))
    obtain ⟨g, hg⟩ := (O.Φ.C c).f0.exists_isMap φ rfl hx
    refine deg_eq_mul_base O c M (fun σ => (h σ).isVB) pbB frE hfb arY' V ρ rfl hcov jG c1 c2 g
      ⟨by simp only [Category.assoc, c1]; rfl, rfl, hχ, fun σ => agreeAt_of_isFrameSecX σ (h σ).isVB (frE σ) (fl σ) c1 hχ g hg
        fun i => ⟨_, hr σ i⟩⟩ ?_ β hβ
    change (O.Φ.C c).Carries (genPt Gs ≫ πG) g
    rw [hφ]
    exact GlobalTheory.T.flag_compactification_function_field _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) Gs.functionField φ _ _ g rfl hx hg
  · have hl : letterOf O.S.Dw (.inl (z.1, (z.2 : ℕ))) = some ⟨z.1, z.2⟩ := by
      simp [letterOf, z.2.isLt]
    have hind : V.Induces (lineAdl O R c (.inl (z.1, (z.2 : ℕ))) 1)
        (VMetric.grLB ((fl z.1).pull ρ) z.2 (((H z.1).pull π rfl).pull ρ rfl)) 1 := by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.pair_cover_hodge_comparison p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1) (H z.1) (t z.1)
        (frE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) _ hl
      exact ⟨r z.1 z.2, h1, h2,
        fun τ zc y y' ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_metric p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1)
          (H z.1) (t z.1) (frE z.1) (metE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) _ hl τ zc y y' ch e1 e2 hc,
        fun v e y zg yt ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_degree p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1)
          (H z.1) (t z.1) (frE z.1) (latE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) v e y zg yt ch e1 e2 hc⟩
    exact GlobalTheory.InducesIsom.induces_of_isometric V _ _ _ 1 hind
      (VMetric.isometric_grLB_pull (𝓞 D.what₂.LL) Y X (π ≫ q) (ρ ≫ π ≫ q) _ _ ((h z.1).pull π rfl) ((H z.1).pull π rfl)
        (fl z.1) ρ rfl z.2)
  · have hl : letterOf O.S.Dw (.inr k) = some ⟨z.1, z.2⟩ := hk
    obtain ⟨h1, h2⟩ := GlobalTheory.T.pair_cover_hodge_comparison p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1) (H' z.1)
      (t' z.1) (frE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) _ hl
    exact ⟨r' z.1 z.2, h1, h2,
      fun τ zc y y' ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_metric p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1)
        (H' z.1) (t' z.1) (frE' z.1) (metE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) _ hl τ zc y y' ch e1 e2 hc,
      fun v e y zg yt ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_height p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1)
        (H' z.1) (t' z.1) (frE' z.1) (latE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) k hk v e y zg yt ch e1 e2 hc⟩

end GlobalTheory.FlagCovDeg

end
