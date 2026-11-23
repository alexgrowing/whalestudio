import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFracChart

theorem isFractionRing_and_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens)
    (hUV : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (hρ : spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι) :
    (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧
      ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  set V := barComp TF.Y Z
  set W : (X₀ TF.Y Z).Opens := V.ι ⁻¹ᵁ U.1 with hWdef
  have hU : IsAffineOpen U.1 := U.2
  have hWU : V.ι ''ᵁ W = U.1 := by
    rw [hWdef, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUV
  have hW : IsAffineOpen W := by
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, hWU]; exact hU
  have hch : LogKS.chart U = hU.fromSpec := rfl
  have hcomp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g) x = g (f x) := fun _ _ _ => rfl
  have hη : genericPoint (X₀ TF.Y Z) ∈ W := by
    obtain ⟨p⟩ : Nonempty (Sp (X₀ TF.Y Z).functionField) := inferInstance
    have h1 : (spMap ρ ≫ LogKS.chart U) p ∈ U.1 := by
      rw [hcomp, hch]; show _ ∈ (U.1 : Set TF.Y.X); rw [← hU.range_fromSpec]; exact Set.mem_range_self _
    rw [hρ, hcomp] at h1
    exact GlobalTheory.Cartier.gen_mem (x := GlobalTheory.LogKSDiv.genPt TF Z p) h1
  set σ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField :=
    ((X₀ TF.Y Z).presheaf.germ W _ hη).hom.comp (V.ι.appLE U.1 W le_rfl).hom with hσ
  have key : spMap ρ ≫ hU.fromSpec = spMap σ ≫ hU.fromSpec := by
    rw [← hch, hρ, GlobalTheory.LogKSDiv.genPt, ← hW.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec V.ι hU hW le_rfl, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hρe : ρ = σ := by
    have := Spec.map_injective ((cancel_mono hU.fromSpec).1 key)
    exact congrArg CommRingCat.Hom.hom this
  subst hρe
  haveI : Nonempty W := ⟨⟨_, hη⟩⟩
  have hle : U.1 ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hUV
  haveI : IsIso (V.ι.app U.1) := Scheme.Hom.isIso_app V.ι U.1 hle
  have hFr : IsFractionRing Γ(X₀ TF.Y Z, W) (X₀ TF.Y Z).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ W hW
  refine ⟨?_, ?_⟩
  · letI := σ.toAlgebra
    exact IsFractionRing.of_ringEquiv_left (asIso (V.ι.app U.1)).commRingCatIsoToRingEquiv (fun x => by
      show σ x = _
      simp only [σ, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
      rfl)
  · intro a
    rw [← GlobalTheory.Cartier.fnOf_comp_algX (s₀ TF.Y Z) W hη]
    simp only [σ, RingHom.comp_apply]
    congr 1
    show ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ TF.Y.s.appLE ⊤ U.1 (fun _ _ => trivial) ≫
      V.ι.appLE U.1 W le_rfl).hom a = _
    have e := Scheme.Hom.appLE_comp_appLE V.ι TF.Y.s ⊤ U.1 W (fun _ _ => trivial) le_rfl
    erw [e]
    rfl

end GlobalTheory.GenFracChart
