import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo.AlgPtHom

theorem germTop_stalkClosedPointTo {R : CommRingCat.{0}} [IsLocalRing R] {Z : Scheme.{0}} (f : Spec R ⟶ Z) :
    Z.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso R).hom := by
  refine (Scheme.germ_stalkClosedPointTo f ⊤ trivial).trans ?_
  have h : ∀ (p : (⊤ : (Spec R).Opens) = ⊤), (Functor.mapIso (Spec R).presheaf (eqToIso p).op).hom = 𝟙 _ := by
    intro p
    simp
  simp only [Iso.trans_hom]
  erw [h rfl, Category.id_comp]
  rfl

theorem exists_evalHom : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Y.X.Opens) (y : AlgPt Y) (hx : below y.1 ∈ V),
    ∃ φ : Γ(Y.X, V) →+* AlgebraicClosure F,
      (∀ a, valAt y.1 (fnOf V (gen_mem hx) a) = φ a) ∧
      (∀ b, below y.1 ∉ Y.X.basicOpen b → φ b = 0) ∧
      ∀ c : F, φ ((Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (algebraMap F Γ(Y.X, ⊤) c)) =
        algebraMap F (AlgebraicClosure F) c := by
  intro F _ _ Y V y hx
  refine ⟨(Scheme.stalkClosedPointTo (R := .of (AlgebraicClosure F)) y.1).hom.comp
    (Y.X.presheaf.germ V (below y.1) hx).hom, ?_, ?_, ?_⟩
  · intro a
    rw [← algebraMap_germ hx a, Base.valAt_stalk]
    rfl
  · intro b hb
    rw [Scheme.mem_basicOpen _ _ _ hx] at hb
    by_contra hne
    exact hb (isUnit_of_map_unit (Scheme.stalkClosedPointTo (R := .of (AlgebraicClosure F)) y.1).hom _
      (isUnit_iff_ne_zero.mpr hne))
  · intro c
    have e1 : Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ Y.X.presheaf.germ V (below y.1) hx =
        Y.X.presheaf.germ ⊤ (below y.1) trivial := TopCat.Presheaf.germ_res _ _ _ _
    have e2 := germTop_stalkClosedPointTo (R := .of (AlgebraicClosure F)) y.1
    have e3 : Y.str.appTop ≫ y.1.appTop = (spMap (algebraMap F (AlgebraicClosure F))).appTop := by
      rw [← Scheme.Hom.comp_appTop, y.2]
    have e4 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))
    have e5 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ Y.str.appTop ≫
        (Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ Y.X.presheaf.germ V (below y.1) hx) ≫
        Scheme.stalkClosedPointTo (R := .of (AlgebraicClosure F)) y.1 =
        CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) := by
      rw [e1]
      erw [e2]
      rw [← Category.assoc Y.str.appTop]
      erw [e3, e4]
      rw [Iso.inv_hom_id_assoc]
    rw [Var.algebraMap_Γ]
    exact congrArg (fun q => q.hom c) e5

end GlobalTheory.TrueGeo.AlgPtHom
