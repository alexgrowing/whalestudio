import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
open CategoryTheory.Limits
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagGenFib
variable {D : D7} {Bs Y₀ : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (π₀ : Y₀ ⟶ Bs)

def Gf : Scheme.{0} := pullback (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))

def jf : Gf q π₀ ⟶ Y₀ := pullback.fst _ _

def sf : Gf q π₀ ⟶ Sp D.what₂.LL := pullback.snd _ _

theorem isPullback_f :
    IsPullback (jf q π₀) (sf q π₀) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) :=
  IsPullback.of_hasPullback _ _

def jGf {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (p : Bg ⟶ Sp D.what₂.LL)
    (hB : IsPullback jB p q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) : Gf q π₀ ⟶ Bg :=
  hB.lift (jf q π₀ ≫ π₀) (sf q π₀) (by
    simpa [Category.assoc] using (isPullback_f q π₀).w)

theorem jGf_jB {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (p : Bg ⟶ Sp D.what₂.LL)
    (hB : IsPullback jB p q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) :
    jGf q π₀ jB p hB ≫ jB = jf q π₀ ≫ π₀ :=
  hB.lift_fst _ _ _

theorem exists_ringHom_of_generic {G X : Scheme.{0}} [IsIntegral G] [IsIntegral X] (f : G ⟶ X)
    (hf : f (genericPoint G) = genericPoint X) :
    ∃ φ : X.functionField →+* G.functionField,
      G.fromSpecStalk (genericPoint G) ≫ f = spMap φ ≫ X.fromSpecStalk (genericPoint X) := by
  have h : f (genericPoint G) ⤳ genericPoint X := by rw [hf]
  refine ⟨(X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint G)).hom, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint G)).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem surjective_of_generic {G X : Scheme.{0}} [IsIntegral G] [IsIntegral X] (f : G ⟶ X) [IsFinite f]
    (hf : f (genericPoint G) = genericPoint X) : Surjective f := by
  refine ⟨fun x => ?_⟩
  have hc : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hx : x ∈ closure {genericPoint X} := by
    have := genericPoint_spec X
    rw [this.def]; trivial
  have hsub : closure {genericPoint X} ⊆ Set.range f.base :=
    closure_minimal (by rintro _ rfl; exact ⟨_, hf⟩) hc
  exact hsub hx

end GlobalTheory.FlagGenFib
