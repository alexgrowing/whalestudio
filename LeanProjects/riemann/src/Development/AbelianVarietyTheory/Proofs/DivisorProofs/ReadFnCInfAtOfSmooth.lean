import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt

namespace ReadFunctionSmooth
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.ReadFn

theorem cInfAt_readFn : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e)
    (I : ManIs M Y) (f : M.Fun), M.Smooth f → ∀ σ y, CInfAt (readFn I f σ) y := by
  intro F _ _ Y e M I f hf σ y
  obtain ⟨a, rfl⟩ := I.ε.surjective σ
  have hA := isAlgAtlas_tAtlas I a
  have hs : (tAtlas (M.A a) (I.pt a)).Smooth (readFn I f (I.ε a)) := by
    intro j
    have e₁ : readFn I f (I.ε a) ∘ ((tAtlas (M.A a) (I.pt a)).chart j).symm =
        f a ∘ ((M.A a).chart j).symm := funext fun v => by
      rw [Function.comp_apply, tAtlas_symm, readFn_apply, Function.comp_apply]
    have e₂ : ((tAtlas (M.A a) (I.pt a)).chart j).target ∩
        ((tAtlas (M.A a) (I.pt a)).chart j).symm ⁻¹' Set.univ =
        ((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' Set.univ := by
      simp only [Set.preimage_univ, Set.inter_univ, tAtlas_target]
    rw [e₁, e₂]
    exact hf a j
  exact (CxPts.cInfAt_iff_smoothOn hA.anRead isOpen_univ).2 ((hA.smooth_iff hA.anRead).1 hs) y
    (Set.mem_univ y)

end GlobalTheory.CompanionTheory.ReadFn

end

end ReadFunctionSmooth
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.readFn_cInfAt_of_smooth : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (f : M.Fun), M.Smooth f → ∀ σ y, CInfAt (readFn I f σ) y := by
  first | exact @ReadFunctionSmooth.GlobalTheory.CompanionTheory.ReadFn.cInfAt_readFn | exact ReadFunctionSmooth.GlobalTheory.CompanionTheory.ReadFn.cInfAt_readFn | (intros; apply ReadFunctionSmooth.GlobalTheory.CompanionTheory.ReadFn.cInfAt_readFn <;> assumption)

end
