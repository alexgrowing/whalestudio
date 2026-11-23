import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem res_res_frameRestrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isFrame_restrict : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  intro X C _ V hV L u C' _ V' hV' H hH ⟨τ, hgen, hcomp⟩
  refine ⟨fun T m ↦ res (inf_le_inf_right (L.U m) (hH T)) (τ (H.obj T) m), fun T m m' ↦ ?_, fun T T' a m ↦ ?_⟩
  · have key := congrArg (res (inf_le_inf_right (L.U m') (inf_le_inf_right (L.U m) (hH T)))) (hgen (H.obj T) m m')
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key
  · have key := congrArg (res (inf_le_inf_right (L.U m) (hH T'))) (hcomp (H.obj T) (H.obj T') (H.map a) m)
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key

end GlobalTheory.LBObs
