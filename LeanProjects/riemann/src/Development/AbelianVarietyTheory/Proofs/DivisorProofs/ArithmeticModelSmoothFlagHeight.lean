import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase.MetSmooth

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CxPts

section Lift

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ}

theorem exists_app_eq (r : Y' ⟶ Y) [IsPreimmersion r] {U : Y'.Opens} (g : Γ(Y', U)) {w : Y'} (hw : w ∈ U) :
    ∃ (V : Y.Opens) (g₀ : Γ(Y, V)) (h : r ⁻¹ᵁ V ≤ U), w ∈ r ⁻¹ᵁ V ∧ r.app V g₀ = resG Y' h g := by
  obtain ⟨a, ha⟩ := r.stalkMap_surjective w (Y'.presheaf.germ U w hw g)
  obtain ⟨V₀, hV₀, g₀, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [Scheme.Hom.germ_stalkMap_apply] at ha
  obtain ⟨T, hT, i₁, i₂, e⟩ := Y'.presheaf.germ_eq w _ _ _ _ ha
  obtain ⟨V₁, hV₁, e₁⟩ := r.isEmbedding.isInducing.isOpen_iff.1 T.isOpen
  have hle : r ⁻¹ᵁ (V₀ ⊓ ⟨V₁, hV₁⟩) ≤ T := fun x hx => by
    have : x ∈ r ⁻¹' V₁ := hx.2
    rwa [e₁] at this
  have hw₁ : w ∈ r ⁻¹' V₁ := by rw [e₁]; exact hT
  refine ⟨V₀ ⊓ ⟨V₁, hV₁⟩, resG Y inf_le_left g₀, hle.trans i₂.le, ⟨hV₀, hw₁⟩, ?_⟩
  have e₂ := congrArg (resG Y' hle) e
  have e₃ : r.app (V₀ ⊓ ⟨V₁, hV₁⟩) (resG Y inf_le_left g₀) = resG Y' (hle.trans i₁.le) (r.app V₀ g₀) :=
    congr($(r.naturality (homOfLE (inf_le_left : V₀ ⊓ ⟨V₁, hV₁⟩ ≤ V₀)).op) g₀)
  exact e₃.trans ((LB.resG_resG _ _ _).symm.trans (e₂.trans (LB.resG_resG _ _ _)))

variable {r : Y' ⟶ Y} [IsPreimmersion r] {L : CxPts p σ → CxPts p' σ'}

theorem exists_ev_lift (hL : ∀ z, (L z).1 ≫ r = z.1) {U : Y'.Opens} (g : Γ(Y', U)) {z : CxPts p σ}
    (hz : L z ∈ ptsIn p' σ' U) : ∃ (V : Y.Opens) (g₀ : Γ(Y, V)), z ∈ ptsIn p σ V ∧
      ∀ w ∈ ptsIn p σ V, L w ∈ ptsIn p' σ' U ∧ ev p' σ' U g (L w) = ev p σ V g₀ w := by
  obtain ⟨V, g₀, h, hw, e⟩ := exists_app_eq r g (mem_ptsIn.1 hz)
  have key (w : CxPts p σ) : L w ∈ ptsIn p' σ' (r ⁻¹ᵁ V) ↔ w ∈ ptsIn p σ V := by
    change _ ↔ ⊤ ≤ w.1 ⁻¹ᵁ V
    rw [← hL w]
    rfl
  refine ⟨V, g₀, (key z).1 (mem_ptsIn.2 hw), fun w hw => ⟨ptsIn_mono h ((key w).2 hw), ?_⟩⟩
  rw [← ev_res h ((key w).2 hw), ← e, ev, ev, ← hL w]
  exact (Points.valR_comp _ _ _ _).symm

theorem continuous_lift (hL : ∀ z, (L z).1 ≫ r = z.1) : Continuous L := by
  refine CxPts.continuous_iff.2 fun U => ⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun g z hz => ?_⟩
  · obtain ⟨V, g₀, h₁, h₂⟩ := exists_ev_lift hL (0 : Γ(Y', U)) hz
    filter_upwards [(isOpen_ptsIn V).mem_nhds h₁] with w hw using (h₂ w hw).1
  · obtain ⟨V, g₀, h₁, h₂⟩ := exists_ev_lift hL g hz
    refine (((continuousOn_ev g₀).continuousAt ((isOpen_ptsIn V).mem_nhds h₁)).congr ?_).continuousWithinAt
    filter_upwards [(isOpen_ptsIn V).mem_nhds h₁] with w hw using (h₂ w hw).2.symm

theorem vInfAt_lift (hL : ∀ z, (L z).1 ≫ r = z.1) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : CxPts p' σ' → G} {z : CxPts p σ} (h : VInfAt f (L z)) : VInfAt (fun w => f (L w)) z := by
  obtain ⟨U, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hg : VInfAt (fun w a => ev p' σ' U (g a) (L w)) z := vInfAt_pi fun a => by
    obtain ⟨V, g₀, h₁, h₂⟩ := exists_ev_lift hL (g a) h₁
    refine (vInfAt_ev g₀ h₁).congr ?_
    filter_upwards [(isOpen_ptsIn V).mem_nhds h₁] with w hw using (h₂ w hw).2
  exact (hg.comp h₂ h₃ h₄).congr ((continuous_lift hL).continuousAt.eventually h₅)

omit [IsPreimmersion r] in

theorem vInfAt_comp {m : CxPts p' σ' → CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ r) {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : CxPts p σ → G} {z : CxPts p' σ'} (h : VInfAt f (m z)) : VInfAt (fun w => f (m w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨r ⁻¹ᵁ W, ι, inferInstance, fun a => r.app W (g a), F, O, (mem_ptsIn_preimage hm).2 h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_of_comp hm] using h₃
  · simp only [← ev_of_comp hm]
    exact (continuous_of_comp hm).continuousAt.eventually h₅

omit [IsPreimmersion r] in

theorem vInfAt_of_re_im {f : CxPts p σ → ℂ} {z : CxPts p σ} (h₁ : CInfAt (fun w => (f w).re) z)
    (h₂ : CInfAt (fun w => (f w).im) z) : VInfAt f z := by
  have := ((vInfAt_iff_cInfAt.2 h₁).prodMk (vInfAt_iff_cInfAt.2 h₂)).comp_contDiff
    Complex.equivRealProdCLM.symm.contDiff
  exact this.congr (.of_forall fun w => by simp [Complex.equivRealProdCLM_symm_apply])

end Lift

theorem exists_extend {F : Type} [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) :
    ∃ σ' : F →+* ℂ, σ'.comp (algebraMap (𝓞 F) F) = σ := by
  have hi : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  refine ⟨IsFractionRing.lift (A := 𝓞 F) (K := F) hi, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

section Gram

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.VB GlobalTheory.LieMet Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem exists_frame_replace {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (f : EigFrame Z φ x)
    (τ : E →+* ℂ) {u : Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) :
    ∃ g : EigFrame Z φ x, g.v τ = u := by
  classical
  have key (τ' : E →+* ℂ) : IsEigBasis Z φ x τ' (Function.update f.v τ u τ') := by
    rcases eq_or_ne τ' τ with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      exact ⟨fun i => ⟨f.tan τ' i, f.eig τ' i⟩, fun w hw => f.basis τ' w hw.1 hw.2⟩
  exact ⟨⟨Function.update f.v τ u, fun τ' i => ((key τ').1 i).1, fun τ' i => ((key τ').1 i).2,
    fun τ' w h₁ h₂ => (key τ').2 w ⟨h₁, h₂⟩⟩, Function.update_self τ u f.v⟩

variable {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)

theorem over_symm {K : Type} [CommRing K] {x : Sp K ⟶ W} {ψ : F →+* K}
    (h : x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) :
    (x ≫ πB) ≫ genStr Z = spMap (ψ.comp e.symm.toRingHom) := by
  have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.apply_symm_apply))
  rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← h]
  simp only [Category.assoc, h1, Category.comp_id]

def down {σ : F →+* ℂ} (w : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ) :
    CxPts (genStr Z) (σ.comp e.symm.toRingHom) := ⟨w.1 ≫ πB, over_symm e πB w.2⟩

theorem exists_gram [SmoothOfRelativeDimension Dw.dim (genStr Z)] {M : X.Modules} {τ : E →+* ℂ} {dual : Bool}
    {uu : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ dual uu) {σ : F →+* ℂ}
    {G : EigMet Z (σ.comp e.symm.toRingHom)} (hG : G.SmoothOn (manifold Z _) Set.univ) (ch : Chart M (Dw.mult τ))
    {w₀ : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ} (h₀ : w₀ ∈ ptsIn _ σ (jB ⁻¹ᵁ ch.U)) :
    ∃ N : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ,
      MInfAt N w₀ ∧ ∀ᶠ w : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ in 𝓝 w₀,
      ∃ (hx : (⊤ : (Sp ℂ).Opens) ≤ (w.1 ≫ jB) ⁻¹ᵁ ch.U)
        (g : EigFrame Z (σ.comp e.symm.toRingHom) ((down e πB w).1 ≫ genι Z)),
        (∀ i, g.v τ i = uu ch.U ch.e ch.isFrame ℂ w.1 hx i) ∧ (G.gram (down e πB w) g τ)ᵀ = N w := by
  obtain ⟨U, hU, φ, Φ, hzU, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c Oz β Z
    ((down e πB w₀).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hm : ∀ w : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ, (down e πB w).1 = w.1 ≫ πB := fun _ => rfl
  have hyV : down e πB w₀ ∈ ptsIn (genStr Z) _ V.1 := mem_ptsIn.2 hzU
  obtain ⟨A, hA, hwA, hAle⟩ := Opens.isBasis_iff_nbhd.1 W.isBasis_affineOpens
    (mem_ptsIn.1 (mem_ptsIn_inf.2 ⟨h₀, (mem_ptsIn_preimage hm).2 hyV⟩))
  let A' : W.affineOpens := ⟨A, hA⟩
  have hA₁ : A ≤ jB ⁻¹ᵁ ch.U := hAle.trans inf_le_left
  have hA₂ : A ≤ πB ⁻¹ᵁ U := hAle.trans inf_le_right
  let x : Sp Γ(W, A) ⟶ W := LogKS.chart A'
  let ρ : Γ(gen Z, U) →+* Γ(W, A) := (πB.appLE U A hA₂).hom
  have hρ : spMap ρ ≫ LogKS.chart V = x ≫ πB := IsAffineOpen.SpecMap_appLE_fromSpec πB hU hA hA₂
  let ψ : F →+* Γ(W, A) := (Spec.preimage (x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom
  have hψ : x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ := (Spec.map_preimage _).symm
  have hxU : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ ch.U := fun t _ => hA₁ (hA.range_fromSpec.le ⟨t, rfl⟩)
  have hφρ : ψ.comp e.symm.toRingHom = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← over_symm e πB hψ, ← hρ, Category.assoc, hφ', ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap])
  obtain ⟨Φ', hΦ'⟩ := Φ.exists_isMap ρ hφρ (x' := x ≫ πB ≫ genι Z) (by
    rw [← Category.assoc, ← hρ, Category.assoc]; rfl)
  obtain ⟨g, hg⟩ := exists_frame_replace Φ' τ (hu.1 ch.U ch.e ch.isFrame _ x hxU ψ hψ)
  choose γ hre him hγ using fun a b => hG V φ Φ τ a b hφ'
  have hT : IsOpen (Set.univ ∩ ptsIn (genStr Z) (σ.comp e.symm.toRingHom) V.1) := isOpen_univ.inter (isOpen_ptsIn _)
  have hγ' (a b) : VInfAt (fun w => γ a b (down e πB w)) w₀ := vInfAt_comp hm (vInfAt_of_re_im
    ((cInfAt_iff_smoothOn _ hT).2 (hre a b) _ ⟨trivial, hyV⟩) ((cInfAt_iff_smoothOn _ hT).2 (him a b) _ ⟨trivial, hyV⟩))
  refine ⟨fun w => HermFrame.chg (of fun a b => ev _ σ A (Φ'.co g τ a b) w) (of fun a b => γ b a (down e πB w)),
    MInfAt.chg (fun a b => vInfAt_ev _ (mem_ptsIn.2 hwA)) fun a b => hγ' b a, ?_⟩
  filter_upwards [(isOpen_ptsIn A).mem_nhds (mem_ptsIn.2 hwA)] with w hw
  have hwx : spMap (evHom hw) ≫ x = w.1 := spMap_evHom (V := A') hw
  have hwV : down e πB w ∈ ptsIn (genStr Z) _ V.1 := (mem_ptsIn_preimage hm).1 (ptsIn_mono hA₂ hw)
  have h₁ : σ.comp e.symm.toRingHom = (evHom hw).comp (ψ.comp e.symm.toRingHom) := EigLoc.spMap_inj (by
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (evHom hw), ← over_symm e πB hψ, ← (down e πB w).2, hm, ← hwx]
    simp only [Category.assoc])
  have h₂ : (down e πB w).1 ≫ genι Z = spMap (evHom hw) ≫ x ≫ πB ≫ genι Z := by
    rw [hm, ← hwx]; simp only [Category.assoc]
  obtain ⟨f', hf'⟩ := Φ'.exists_isMap (evHom hw) h₁ h₂
  obtain ⟨g', hg'⟩ := g.exists_isMap (evHom hw) h₁ h₂
  have h₃ : evHom hwV = (evHom hw).comp ρ := RingHom.ext fun a => by
    rw [RingHom.comp_apply, ← ev_eq, ← ev_eq]
    exact (ev_of_comp hm U a w).trans (ev_res hA₂ hw _).symm
  have hf'' : Φ.IsMap (evHom hwV) f' := fun τ' i => by
    rw [hf' τ' i, hΦ' τ' i, h₃, GlobalTheory.GradedPieces.dual_comp]
  have hx : ⊤ ≤ (w.1 ≫ jB) ⁻¹ᵁ ch.U := ptsIn_mono hA₁ hw
  refine ⟨hx, g', fun i => ?_, ?_⟩
  · have := hu.2.2 ch.U ch.e ch.isFrame _ ℂ (evHom hw) x hxU (hwx ▸ hx) i
    rw [hg' τ i, hg, ← this]
    congr 1
  · rw [G.change _ f' g', hf'.co τ hg' h₂, HermFrame.chg, transpose_mul, transpose_mul, Matrix.mul_assoc]
    have e₁ : (of fun a b => ev _ σ A (Φ'.co g τ a b) w) = (Φ'.co g τ).map (evHom hw) :=
      Matrix.ext fun a b => ev_eq hw _
    have e₂ : (of fun a b => γ b a (down e πB w)) = (G.gram _ f' τ)ᵀ :=
      Matrix.ext fun a b => (hγ b a _ trivial hwV f' hf'').symm
    rw [e₁, e₂]

end Gram

end GlobalTheory.ArLieBase.MetSmooth

end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

open scoped ComplexOrder in

theorem GlobalTheory.ArLieBase.isCInf_of_isLieMet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → ∀ (M : X.Modules) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (hr : r = Dw.mult τ) (uu : FrAssign Z M r jB) (G : ∀ σ', EigMet Z σ') (h : VMetric q M r), IsLieFrames Z e jB πB M r τ dual uu → (∀ σ', (G σ').SmoothOn (manifold Z σ') Set.univ) → IsLieMet Z e q jB πB M r τ dual hr G h uu → h.IsCInf := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W _ q jB πB hP M r τ dual hr uu G h hu hG hh σ₀
  subst hr
  obtain ⟨σ, rfl⟩ := MetSmooth.exists_extend σ₀
  have h1 : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion jB := MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip h1
  have hw (z : CxPts q (σ.comp (algebraMap (𝓞 F) F))) : z.1 ≫ q = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    z.2.trans (ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap _ _).symm
  let L (z : CxPts q (σ.comp (algebraMap (𝓞 F) F))) : CxPts (πB ≫ genStr Z ≫ spMap e.toRingHom) σ :=
    ⟨hP.lift z.1 (spMap σ) (hw z), hP.lift_snd _ _ _⟩
  have hL : ∀ z, (L z).1 ≫ jB = z.1 := fun z => hP.lift_fst _ _ _
  intro ch z hz
  obtain ⟨N, hN, hev⟩ := MetSmooth.exists_gram e jB πB hu (hG _) ch (w₀ := L z) (by
    change ⊤ ≤ ((L z).1 ≫ jB) ⁻¹ᵁ ch.U
    rw [hL]; exact hz)
  have hN' : CxPts.MInfAt (fun w => N (L w)) z := fun a b => MetSmooth.vInfAt_lift hL (hN a b)
  have hev' := (MetSmooth.continuous_lift hL).continuousAt.eventually hev
  cases dual with
  | false =>
    refine hN'.congr ?_
    filter_upwards [hev'] with w ⟨hx, g, h₁, h₂⟩
    exact (hh σ w (L w).1 (MetSmooth.down e πB (L w)) (hL w) rfl ch hx g h₁).trans h₂
  | true =>
    obtain ⟨-, g₀, -, hg₀⟩ := hev.self_of_nhds
    refine (hN'.dualGram ?_).congr ?_
    · rw [← hg₀, Matrix.det_transpose]
      exact (Matrix.isUnit_iff_isUnit_det _).1 ((G _).pos _ _ _).isUnit
    filter_upwards [hev'] with w ⟨hx, g, h₁, h₂⟩
    rw [hh σ w (L w).1 (MetSmooth.down e πB (L w)) (hL w) rfl ch hx g h₁, ← h₂, HermFrame.dualGram,
      ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    rfl
