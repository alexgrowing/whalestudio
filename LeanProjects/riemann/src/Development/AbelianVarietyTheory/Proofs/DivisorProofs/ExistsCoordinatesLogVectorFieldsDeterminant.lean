import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncStalkRegularParametersFromAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

theorem GlobalTheory.LogPole.exists_coord_logDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  intro E _ _ _ H Dw l Xo c TF U b x₀ hx₀
  classical
  have hres : ∀ (V W : TF.Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ V) (hVU : V ≤ U.1)
      (f : Fin Dw.dim → Γ(TF.Y.X, U.1)), TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hVU (f i)) →
      TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X (h.trans hVU) (f i)) := by
    intro V W hW h hVU f hf
    have h' := hf.res hW h
    rw [TopForm.resForm_dOn] at h'
    simpa only [LB.resG_resG] using h'
  obtain ⟨hreg, m, a, J, hRsp, hIa⟩ := GlobalTheory.T.snc_stalk_regularParameters_from_affineOpen TF.Y.X (LogKS.boundary TF.Y) TF.snc U x₀ hx₀
  haveI := TF.smooth
  obtain ⟨hfp, hfree, hfin, hrank⟩ := GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (algX TF.Y.s U.1).toAlgebra
  letI : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨x₀, hx₀⟩
  letI : Algebra c.F (TF.Y.X.presheaf.stalk x₀) :=
    ((TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom.comp (algX TF.Y.s U.1)).toAlgebra
  haveI : IsScalarTower c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hloc := U.2.isLocalization_stalk ⟨x₀, hx₀⟩
  haveI : IsNoetherianRing Γ(TF.Y.X, U.1) := Algebra.FiniteType.isNoetherianRing c.F _
  haveI : IsNoetherianRing (TF.Y.X.presheaf.stalk x₀) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal.primeCompl _ inferInstance
  have h3 := GlobalTheory.T.exists_coordinates_extending_regular_parameters c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal Dw.dim hrank m a hRsp
  obtain ⟨x, e, hxe, bs, hbs⟩ := h3
  have hxe' : (fun j => x (e j)) = a := funext hxe
  have hI : ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (∏ j ∈ J, x (e j))} := by
    simp only [hxe]; exact hIa
  have hspan : ∀ D : Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1),
      (∀ c', D (algebraMap c.F Γ(TF.Y.X, U.1) c') = 0) → (∀ f ∈ (LogKS.boundary TF.Y).ideal U, D f ∈ (LogKS.boundary TF.Y).ideal U) →
      ∃ cf : Fin Dw.dim → Γ(TF.Y.X, U.1), D = ∑ j, cf j • (b j).1 := by
    intro D h0 h1
    let D' : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := ⟨D, h0, h1⟩
    refine ⟨b.repr D', ?_⟩
    have := congrArg Subtype.val (b.sum_repr D')
    rw [Submodule.coe_sum] at this
    exact this.symm
  have h4 := GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal
    Dw.dim m x e J (by simp only [hxe]; exact hRsp) ⟨bs, hbs⟩ ((LogKS.boundary TF.Y).ideal U) hI
    (fun j => (b j).1) (fun j c' => (b j).2.1 c') (fun j => (b j).2.2) hspan
  obtain ⟨u, hu⟩ := h4
  have hd : ((LogKS.boundary TF.Y).ideal U).map (TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom =
      Ideal.span {(TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom (logDet (fun j => (b j).1) x)} := by
    change ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (logDet (fun j => (b j).1) x)}
    exact hI.trans ((Ideal.span_singleton_mul_left_unit u.isUnit _).symm.trans (congrArg (fun y => Ideal.span {y}) hu.symm))
  have h5 := GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal TF.Y.X (LogKS.boundary TF.Y) U x₀ hx₀ _ inferInstance hd
  obtain ⟨s₂, hs₂, hid⟩ := h5
  have h2 := GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀ x ⟨bs, hbs⟩
  obtain ⟨s₁, hs₁, hfr⟩ := h2
  have hle₁ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₁ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hle₂ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₂ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  refine ⟨x, TF.Y.X.affineBasicOpen (s₁ * s₂), TF.Y.X.basicOpen_le _, ?_, ?_, hid _ hle₂⟩
  · show x₀ ∈ TF.Y.X.basicOpen (s₁ * s₂)
    rw [Scheme.basicOpen_mul]; exact ⟨hs₁, hs₂⟩
  · exact hres _ _ (U.2.basicOpen (s₁ * s₂)) hle₁ _ x hfr
