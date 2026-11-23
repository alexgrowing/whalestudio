import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem exists_rho {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (w : Sp R ⟶ X) (x : X)
    (hx : w (closedPoint R) = x) : ∃ ρ : X.presheaf.stalk x →+* R, spMap ρ ≫ X.fromSpecStalk x = w := by
  subst hx
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) w⟩

private theorem hom_ext' {R : Type} [CommRing R] {X : Scheme.{0}} {x : X} {f g : X.presheaf.stalk x →+* R}
    (h : spMap f ≫ X.fromSpecStalk x = spMap g ≫ X.fromSpecStalk x) : f = g := by
  have h1 : spMap f = spMap g := (cancel_mono (X.fromSpecStalk x)).1 h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

private theorem gen_eq {X : Scheme.{0}} [IsIntegral X] (x : X) :
    spMap (algebraMap (X.presheaf.stalk x) X.functionField) ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

private theorem spm_cmp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem UpperTheory.exists_stalk_point_lift :
    ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Y : Var F) (b : 𝓞 F →+* O) (B : Vert.Model O) (μ : Match Y b B) (k : Type) [Field k] (z : Sp k ⟶ μ.U.toScheme) (y : Sp k ⟶ Y.X), z ≫ μ.h = y → ∃ (ζ : Sp (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) ⟶ μ.U.toScheme) (ρ : Y.X.presheaf.stalk (below y) →+* B.X.presheaf.stalk (below (z ≫ μ.U.ι))), spMap (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom ≫ ζ = z ∧ spMap (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField) ≫ ζ = μ.U.fromSpecStalkOfMem _ μ.mem ∧ ζ ≫ μ.h = spMap ρ ≫ stalkPt Y (below y) ∧ (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField).comp ρ = μ.φ.comp (algebraMap (Y.X.presheaf.stalk (below y)) Y.X.functionField) ∧ (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom.comp ρ = (Scheme.stalkClosedPointTo y).hom ∧ ∀ s : Y.Fn, UnitAt (below y) s → UnitAt (below (z ≫ μ.U.ι)) (μ.φ s) ∧ TrueGeo.valAt (z ≫ μ.U.ι) (μ.φ s) = TrueGeo.valAt y s := by
  intro F _ _ O _ _ _ Y b B μ k _ z y hy
  have hm : below (z ≫ μ.U.ι) ∈ μ.U := (z (closedPoint k)).2
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Sp (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) ⟶ μ.U.toScheme,
      ζ ≫ μ.U.ι = B.X.fromSpecStalk (below (z ≫ μ.U.ι)) :=
    ⟨μ.U.fromSpecStalkOfMem _ hm, Scheme.Opens.fromSpecStalkOfMem_ι _ _ _⟩
  have e1 : spMap (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom ≫ ζ = z := by
    rw [← cancel_mono μ.U.ι, Category.assoc, hζ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of k) (z ≫ μ.U.ι)
  have e2 : spMap (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField) ≫ ζ =
      μ.U.fromSpecStalkOfMem _ μ.mem := by
    rw [← cancel_mono μ.U.ι, Category.assoc, hζ]
    exact (gen_eq _).trans (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _).symm
  have hc : ζ (closedPoint _) = z (closedPoint k) := by
    apply Subtype.ext
    exact (congrArg (fun f => f (closedPoint _)) hζ).trans Scheme.fromSpecStalk_closedPoint
  have hx : (ζ ≫ μ.h) (closedPoint _) = below y := by
    subst hy
    exact congrArg μ.h hc
  obtain ⟨ρ, hρ⟩ := exists_rho (ζ ≫ μ.h) (below y) hx
  have e4 : (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField).comp ρ =
      μ.φ.comp (algebraMap (Y.X.presheaf.stalk (below y)) Y.X.functionField) := by
    apply hom_ext'
    rw [spm_cmp, Category.assoc, hρ, ← Category.assoc, e2]
    refine μ.φ_spec.trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ _) (spm_cmp _ _).symm)
    exact (congrArg (spMap μ.φ ≫ ·) (gen_eq (below y)).symm).trans (Category.assoc _ _ _).symm
  have e5 : (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom.comp ρ = (Scheme.stalkClosedPointTo y).hom := by
    apply hom_ext'
    rw [spm_cmp, Category.assoc, hρ, ← Category.assoc, e1, hy]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of k) y).symm
  refine ⟨ζ, ρ, e1, e2, hρ.symm, e4, e5, ?_⟩
  rintro s ⟨a, ha, rfl⟩
  have e : μ.φ (algebraMap _ Y.X.functionField a) = algebraMap _ B.X.functionField (ρ a) :=
    (RingHom.congr_fun e4 a).symm
  refine ⟨⟨ρ a, ha.map ρ, e.symm⟩, ?_⟩
  exact (congrArg _ e).trans ((TrueGeo.Base.valAt_stalk _ _).trans
    ((RingHom.congr_fun e5 a).trans (TrueGeo.Base.valAt_stalk y a).symm))
