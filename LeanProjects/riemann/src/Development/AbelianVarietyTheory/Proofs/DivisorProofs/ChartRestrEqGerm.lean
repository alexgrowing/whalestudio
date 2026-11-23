import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.Spread'

theorem germ_pt' {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.LogKSDiv.Spread'

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.chartRestr_eq_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hx ρ hρ r
  have hη : (barComp TF.Y Z).ι (genericPoint (X₀ TF.Y Z)) ∈ U.1 := by
    have h := (genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff ((barComp TF.Y Z).ι ⁻¹ᵁ U.1).isOpen
    exact h.2 ⟨x, trivial, hx⟩
  set ψ := (TF.Y.X.presheaf.germ U.1 _ hη ≫ (barComp TF.Y Z).ι.stalkMap (genericPoint (X₀ TF.Y Z))).hom with hψ
  have hg := GlobalTheory.LogKSDiv.Spread'.germ_pt' (barComp TF.Y Z) (genericPoint (X₀ TF.Y Z)) U.2 hη
  have hmono : Mono (LogKS.chart U) := by
    unfold LogKS.chart
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    infer_instance
  have e1 : spMap ρ = spMap ψ := by
    rw [← cancel_mono (LogKS.chart U), hρ]
    exact hg.symm
  have e2 : ρ = ψ := by
    have := Spec.map_injective e1
    exact congrArg CommRingCat.Hom.hom this
  rw [e2, hψ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  change _ = ((X₀ TF.Y Z).presheaf.germ _ x hx ≫ (X₀ TF.Y Z).presheaf.stalkSpecializes _).hom _
  erw [TopCat.Presheaf.germ_stalkSpecializes]
