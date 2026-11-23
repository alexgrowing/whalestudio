import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] {k : Type} [CommRing k]

theorem functionFieldMap_comp_constFn (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] :
    (functionFieldMap f).comp (Cartier.constFn p) = Cartier.constFn (f ≫ p) := by
  ext a
  simp only [RingHom.comp_apply, Cartier.constFn]
  have h1 := algebraMap_germ (X := W) (U := ⊤) (x := f (genericPoint M)) trivial (algX p ⊤ a)
  have h2 := algebraMap_germ (X := M) (U := ⊤) (x := genericPoint M) trivial (algX (f ≫ p) ⊤ a)
  rw [← h1, ← h2, functionFieldMap_algebraMap]
  congr 1
  have e : f.app ⊤ (algX p ⊤ a) = algX (f ≫ p) ⊤ a := by
    simp [algX, Scheme.Hom.appLE]
    rfl
  rw [← e]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial _

def ratPull (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] (n : ℕ) :
    RatForms p n →ₛₗ[functionFieldMap f] RatForms (f ≫ p) n :=
  TopForm.formMap n (functionFieldMap f) (functionFieldMap_comp_constFn p f)

end GlobalTheory.EtaleKlt
