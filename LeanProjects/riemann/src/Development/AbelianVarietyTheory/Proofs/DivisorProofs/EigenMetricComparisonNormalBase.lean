import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelBaseChangeNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricPullbackDualFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHodgeHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightLowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedOfGradedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalNonarchimedeanPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartFrameValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightUpperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedOfLocalAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEigenHodgeMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelHeightSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetAnalyticStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

section
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical

theorem intAdapted_of_inGr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), jB ≫ ρ = πB ≫ genι Z →
    ∀ {M : (E →+* ℂ) → X.Modules} {r : (E →+* ℂ) → ℕ} {g : ℕ} (t : ∀ τ, FrAssign Z (M τ) (r τ) jB),
    (∀ τ, IsLieFrames Z e jB πB (M τ) (r τ) τ false (t τ)) →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U →
    ∀ (f : ∀ τ, Fin (r τ) → Γ(M τ, V)) (hf : ∀ τ, VB.IsFrame (f τ)) (A : ∀ τ, Matrix (Fin g) (Fin (r τ)) Γ(W, jB ⁻¹ᵁ V)),
    (∀ τ, GenCoord Z jB πB (t τ) ch (hf τ) (A τ)) →
    ∀ {K C R : Type} [CommRing K] [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing R]
      (φ : F →+* K) (io : K →+* C) (j : R →+* K) (ψ : R →+* ↥(intO C)), (intO C).subtype.comp ψ = io.comp j →
      ∀ (xg : Sp K ⟶ W) (xt : Sp R ⟶ X), xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap φ → spMap j ≫ xt = xg ≫ jB →
      ⊤ ≤ xt ⁻¹ᵁ V → ∀ (hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V)) (hxg : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V),
      (∀ τ w, IsEigTan Z ((io.comp φ).comp e.symm.toRingHom) (spMap io ≫ xg ≫ πB ≫ genι Z) τ w →
        ((∃ a : Fin (r τ) → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap io ≫ xg ≫ πB ≫ genι Z)
            (fun i => spMap (dualMap io) ≫ t τ V (f τ) (hf τ) _ xg hxg i) a w) ↔
          InGr Z ((io.comp φ).comp e.symm.toRingHom) (spMap io ≫ xg ≫ πB ≫ genι Z)
            (latDR Z.t (spMap io ≫ xg ≫ πB ≫ genι Z)) τ w)) →
      IntAdapted (fun s : Σ τ, Fin (r τ) => (Fintype.equivFin (E →+* ℂ) s.1 : ℕ))
        ((Matrix.of fun b (s : Σ τ, Fin (r τ)) => A s.1 b s.2).map
          (io.comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx))) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB ρ hc M r g t hF ch V hV f hf A hA K C R _ _ _ _ φ io j ψ hψ xg xt
    h₁ h₂ h₃ hx hxg hG
  have hx' : ⊤ ≤ (spMap io ≫ xg) ⁻¹ᵁ (jB ⁻¹ᵁ V) := fun p _ => hx (x := spMap io p) trivial
  have hx'' : ⊤ ≤ ((spMap io ≫ xg) ≫ jB) ⁻¹ᵁ V := hx'
  have hO : spMap (intO C).subtype ≫ spMap ψ ≫ xt ≫ ρ = (spMap io ≫ xg) ≫ πB ≫ genι Z := by
    rw [← hc, Category.assoc, reassoc_of% h₂.symm, ← Category.assoc, ← Category.assoc (spMap io), ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  have hOU : ⊤ ≤ (spMap ψ ≫ xt ≫ ρ) ⁻¹ᵁ ch.U := fun p _ => hV (h₃ (x := spMap ψ p) trivial)
  have hU : ⊤ ≤ ((spMap io ≫ xg) ≫ πB ≫ genι Z) ⁻¹ᵁ ch.U := by
    rw [← hO]
    exact fun p _ => hOU (x := spMap (intO C).subtype p) trivial
  have hb := fun τ => (hF τ).1 V (f τ) (hf τ) _ (spMap io ≫ xg) hx'' (io.comp φ) (by
    rw [Category.assoc, h₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hP : IsTanMat Z ((spMap io ≫ xg) ≫ πB ≫ genι Z) ch
      (fun s : Σ τ, Fin (r τ) => t s.1 V (f s.1) (hf s.1) _ (spMap io ≫ xg) hx'' s.2)
      ((Matrix.of fun b (s : Σ τ, Fin (r τ)) => A s.1 b s.2).map
        (io.comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx))) := fun s hv hV' b =>
    (TangentOrigin.evalPt_spMap_comp io xg _ hx hx' _).symm.trans (hA s.1 _ _ hx'' hx' s.2 hv hV' b)
  refine GlobalTheory.T.integral_adapted_of_graded _ _ (GlobalTheory.T.bijective_mulVec_of_isTanMat_of_isEigBasis Z _ _ ch hU _ hb _ hP)
    (GlobalTheory.T.toroidal_nonarchimedean_point Z _ _ _ hO ch hOU _ hb (fun τ w hw => ?_) _ hP)
  rw [funext fun i => (hF τ).2.2 V (f τ) (hf τ) _ _ io xg hxg hx'' i]
  rw [Category.assoc] at hw ⊢
  exact hG τ w hw

theorem intAdapted_of_isGrLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), jB ≫ ρ = πB ≫ genι Z →
    ∀ {M : (E →+* ℂ) → X.Modules} {r : (E →+* ℂ) → ℕ} {g : ℕ} (t : ∀ τ, FrAssign Z (M τ) (r τ) jB),
    (∀ τ, IsLieFrames Z e jB πB (M τ) (r τ) τ false (t τ)) → (∀ τ, IsGrLat Z e jB πB (M τ) (r τ) τ (t τ)) →
    ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens), V ≤ ρ ⁻¹ᵁ ch.U →
    ∀ (f : ∀ τ, Fin (r τ) → Γ(M τ, V)) (hf : ∀ τ, VB.IsFrame (f τ)) (A : ∀ τ, Matrix (Fin g) (Fin (r τ)) Γ(W, jB ⁻¹ᵁ V)),
    (∀ τ, GenCoord Z jB πB (t τ) ch (hf τ) (A τ)) →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
      (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X), xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ V → ∀ hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      IntAdapted (fun s : Σ τ, Fin (r τ) => (Fintype.equivFin (E →+* ℂ) s.1 : ℕ))
        ((Matrix.of fun b (s : Σ τ, Fin (r τ)) => A s.1 b s.2).map
          ((ioOf (resP v) ε).comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx))) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB ρ hc M r g t hF hG ch V hV f hf A hA v hp ε xg xt h₁ h₂ h₃ hx
  haveI : Fact (resP v).Prime := ⟨hp⟩
  have hψ : ∃ ψ : ε.O →+* ↥(intO ℂ_[resP v]), (intO ℂ_[resP v]).subtype.comp ψ = (ioOf (resP v) ε).comp ε.O.subtype :=
    ⟨((ioOf (resP v) ε).comp ε.O.subtype).codRestrict _ fun a => (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε _).2 a.2,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ := hψ
  exact intAdapted_of_inGr Z e ρ hc t hF ch V hV f hf A hA _ _ _ ψ hψ xg xt h₁ h₂ h₃ hx hx fun τ =>
    GlobalTheory.TwoLat.CoordReg.grLat_at Z (hG τ) v hp ε xg xt h₁ h₂ V (f τ) (hf τ) h₃ hx

end

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

theorem mem_inf_opens {X : Scheme.{0}} {ι : Type} [Fintype ι] {U : ι → X.Opens} {x : X} (h : ∀ i, x ∈ U i) :
    x ∈ (Finset.univ.inf U : X.Opens) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => trivial
  | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨h a, ih⟩

theorem isGraded_lie : ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (M : DRBase O c) (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)) (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf) (u : ∀ σ, E σ ⟶ E' σ), IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → (∀ σ, IsoHom (h σ) (h' σ) (u σ)) → ∀ (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z) (t : ∀ σ, FrAssign O.s.T.Z (E σ) (O.S.Dw.mult σ) jB) (t' : ∀ σ, FrAssign O.s.T.Z (E' σ) (O.S.Dw.mult σ) jB), PairAt O R c q E E' h h' u jB πB t t' (fun σ' => M.x.eigMetAt σ' (some R)) → ∀ (β : B ⟶ M.B) (w : β ≫ strL M = q), jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z → β (genericPoint B) = genericPoint M.B → ∀ h₀ : VMetric (strL M) ((Scheme.Modules.pullback M.b).obj (GlobalTheory.LieVB.omega O.s.T.Z.t.G)) (D.R.f * O.N), SameMet (intEquiv O) ((M.h R).pull M.b rfl) h₀ → IsGraded (h₀.dual.pull β w) (Fintype.equivFin (D.host.E →+* ℂ)) h u := by
  intro D O _ R _ c M B _ q E E' h h' H H' u hq hn _ Bg jB πB t t' hP β w hc _ h₀ hS
  obtain ⟨pb, -, -, hF, hF', hMt, hLat, hGr, -, hMet, -⟩ := hP
  have hω : IsVB (GlobalTheory.LieVB.omega O.s.T.Z.t.G) (D.R.f * O.N) := (M.h R).isVB
  obtain ⟨ℓ, hℓ, hdual, hG⟩ := GlobalTheory.T.metric_pullback_dual_frames (intEquiv O) (M.h R) M.b h₀ hS β w
  have hT : ∀ σ, ∃ T : E σ ⟶ _, TanCoord O.s.T.Z jB πB (t σ) (β ≫ M.b) hℓ T := fun σ =>
    GlobalTheory.T.toroidal_model_height_lower O.s.T.Z O.κ.e (β ≫ M.b) hq pb hc hℓ hω hdual σ (t σ) (h σ).isVB (hF σ) fun ch V hV hA f hf => by
      obtain ⟨A, hAc⟩ := GlobalTheory.T.toroidal_model_height_comparison O.s.T.Z O.κ.e (β ≫ M.b) pb hc σ (t σ) (hF σ) ch V hV hA f hf
      obtain ⟨A₀, rfl⟩ := GlobalTheory.T.toroidal_model_hodge_height O.s.T.Z O.κ.e (β ≫ M.b) hq hn pb hc σ (t σ) (hF σ) (hLat σ) ch V hV hA f hf A hAc
      exact ⟨A₀, hAc⟩
  choose T hT using hT
  refine GlobalTheory.T.graded_of_local_adapted _ _ h T u (fun σ => GlobalTheory.T.toroidal_model_height_integral O.s.T.Z O.κ.e hq pb σ (t σ) (t' σ) (u σ) (h σ).isVB (h' σ).isVB
    (hF σ) (hF' σ) (hMt σ)) (fun x => ?_)
    (GlobalTheory.T.toroidal_model_height_sum O.s.T.Z O.κ.e (β ≫ M.b) pb hc hℓ hω _ _ ?_ t h T hF hMet hT)
  · obtain ⟨U, m, hxU, hm⟩ := hω ((β ≫ M.b) x)
    let ch : VB.Chart (GlobalTheory.LieVB.omega O.s.T.Z.t.G) (D.R.f * O.N) := ⟨U, m, hm⟩
    choose U₁ f₁ hx₁ hf₁ using fun σ => (h σ).isVB x
    choose U₂ f₂ hx₂ hf₂ using fun σ => (h' σ).isVB x
    have hx : x ∈ ((β ≫ M.b) ⁻¹ᵁ U ⊓ (Finset.univ.inf U₁ ⊓ Finset.univ.inf U₂) : B.Opens) :=
      ⟨hxU, mem_inf_opens hx₁, mem_inf_opens hx₂⟩
    obtain ⟨V, hA, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
    have hle' : V ≤ (β ≫ M.b) ⁻¹ᵁ U ⊓ (Finset.univ.inf U₁ ⊓ Finset.univ.inf U₂) := hle
    have hV : V ≤ (β ≫ M.b) ⁻¹ᵁ ch.U := hle'.trans inf_le_left
    have h₁ (σ) : V ≤ U₁ σ := hle'.trans (inf_le_right.trans (inf_le_left.trans (Finset.inf_le (Finset.mem_univ σ))))
    have h₂ (σ) : V ≤ U₂ σ := hle'.trans (inf_le_right.trans (inf_le_right.trans (Finset.inf_le (Finset.mem_univ σ))))
    have hf := fun σ => (hf₁ σ).res (h₁ σ)
    have hf' := fun σ => (hf₂ σ).res (h₂ σ)
    choose A hAc using fun σ => GlobalTheory.T.toroidal_model_height_comparison O.s.T.Z O.κ.e (β ≫ M.b) pb hc σ (t' σ) (hF' σ) ch V hV hA _ (hf' σ)
    obtain ⟨V', hV', hx', hinj, C, C', Q, e₁, e₂, hQ, e₃⟩ := GlobalTheory.T.matrix_regular_adapted_local hq hn pb _ V hA x hxV _
      (intAdapted_of_isGrLat O.s.T.Z O.κ.e (β ≫ M.b) hc t' hF' hGr ch V hV _ hf' A hAc)
    exact ⟨V', hx', GlobalTheory.T.frame_matrix_restriction jB _ T u hV hV' (ℓ ch) (hℓ ch) _ hf _ hf' (Matrix.of fun b s => A s.1 b s.2) (fun σ b i =>
      GlobalTheory.T.toroidal_model_height_upper O.s.T.Z O.κ.e (β ≫ M.b) pb hc σ (t σ) (t' σ) (u σ) (hF σ) (hF' σ) (hMt σ) ch V hV hA _ (hf σ) _ (hf' σ)
        _ _ (hT σ ch V hV hA _ (hf σ)) (hAc σ) b i) hinj C C' Q e₁ (by convert e₂) hQ e₃⟩
  · intro σ z yc hz ch hch uu P hPm
    let y : CxPts O.s.T.Z.s ((σ.comp O.κ.e.symm.toRingHom).comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) :=
      ⟨yc.1 ≫ genι O.s.T.Z, by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, yc.2, ← Spec.map_comp]
        rfl⟩
    have hy : y ∈ CxPts.ptsIn _ _ ch.U := hch
    rw [hG _ _ (RingHom.ext fun a => rfl) z y (by simpa using hz.symm) ch hy]
    exact GlobalTheory.T.dual_eigen_hodge_metric O.s.T.Z _ (M.h R) (M.dual R) _ yc y rfl ch hy uu P hPm
      (GlobalTheory.T.bijective_mulVec_of_isTanMat_of_isEigBasis O.s.T.Z _ _ ch hch uu.v (fun τ => ⟨fun i => ⟨uu.tan τ i, uu.eig τ i⟩,
        fun v hv => uu.basis τ v hv.1 hv.2⟩) P hPm)

end GlobalTheory.LieFilt

end
