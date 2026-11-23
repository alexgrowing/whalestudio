import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiTopUnit

theorem unit_factor {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (y : Y) (c a : (FractionRing R)ˣ) (u : Rˣ)
    (h : c * a = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) :
    (gm (f ≫ jK R) y ⊤ (unitOn u)).val = (gm f y ⊤ (unitOn c)).val * gs (𝟙 Y) y ⊤ (scal f a.val) := by
  let φ : FractionRing R →+* Y.presheaf.stalk y := (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  have e1 : (gm f y ⊤ (unitOn c)).val = φ c.val := by rw [gm_val f y ⊤ trivial]; rfl
  have e2 : gs (𝟙 Y) y ⊤ (scal f a.val) = φ a.val := by rw [gs_eq _ y ⊤ trivial]; rfl
  have e3 : (gm (f ≫ jK R) y ⊤ (unitOn u)).val = φ (algebraMap R (FractionRing R) u.val) := by
    rw [gm_val _ y ⊤ trivial]
    have e := congrArg (fun q => q.hom u.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    show _ = (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom ((f.app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (CommRingCat.ofHom (algebraMap R (FractionRing R)) u.val)))
    rw [e]
    rfl
  rw [e1, e2, e3, ← map_mul, ← Units.val_mul, h]
  rfl

theorem exists_psiOn_top_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  intro R _ _ _ D ga a hs c hc
  choose u hu using hc
  refine ⟨⟨fun χ => LB.pullGen D.P.L _ _ (GlobalTheory.UU.scaleGen (unitOn (u χ)) (ga χ)) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
    fun χ => DVR.pullGen_isGen _ _ _ _ (GlobalTheory.UU.scaleGen_isGen _ (hs χ).1) _,
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)
  have hp := (hs χ).2 (Over.mk ((jK R ⁻¹ᵁ ⊤).ι ≫ jK R)) (Over.homMk (jK R ⁻¹ᵁ ⊤).ι) y J hJ
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  erw [hp]
  rw [unit_factor _ y (c χ) (a χ) (u χ) (hu χ), _root_.mul_assoc]
  rfl

end GlobalTheory.PsiTopUnit
end
