import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeCoh

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k)

def germSec {V : X.Opens} (hη : genericPoint X ∈ V) : Sec s V →+* X.functionField :=
  (X.presheaf.germ V (genericPoint X) hη).hom

theorem semiHom_germSec {V : X.Opens} (hη : genericPoint X ∈ V) :
    letI := ffAlg s; SemiHom (RingHom.id k) (germSec s hη) := by
  letI := ffAlg s
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
  congr 1
  change (X.presheaf.germ V (genericPoint X) hη).hom ((secMap s V).hom r) =
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ V le_top) ≫ _ = _
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem germSec_restrictGlobal_algebraMap {V : X.Opens} (hη : genericPoint X ∈ V) (r : k) :
    letI := algΓ s; letI := ffAlg s
    germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) = algebraMap k X.functionField r := by
  letI := algΓ s; letI := ffAlg s
  change (X.presheaf.germ V (genericPoint X) hη).hom ((X.presheaf.map (homOfLE le_top).op).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
  rfl

def formGerm (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    letI := algΓ s; letI := ffAlg s
    sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField :=
  letI := algΓ s; letI := ffAlg s
  { toFun := fun x ↦ (semiHom_germSec s hη).mDR
      ((toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) : DR k (Sec s V))
    map_add' := fun x y ↦ by
      rw [map_add, map_add, Submodule.coe_add, map_add]
    map_smul' := fun r x ↦ by
      rw [sectionsOn.toΓ_smul]
      have h1 : (toOmEquiv s j hV).symm (restrictGlobal X V (algebraMap k Γ(X, ⊤) r) •
          sectionsOn.toΓ _ _ x) = (show Sec s V from restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) •
          (toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) :=
        (toOmEquiv s j hV).symm.map_smul _ _
      rw [h1, Submodule.coe_smul, SemiHom.mDR_smul]
      change germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) • _ = _
      rw [germSec_restrictGlobal_algebraMap, algebraMap_smul]
      rfl }

def formGermI (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)
    [inst : Algebra k X.functionField] (hinst : inst = ffAlg s) :
    letI := algΓ s; sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField := by
  subst hinst; exact formGerm s j hV hη

theorem formGermI_ffAlg (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    formGermI (inst := ffAlg s) s j hV hη rfl = formGerm s j hV hη := rfl

example (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    letI := algΓ s; formGerm s j hV hη 0 = 0 := map_zero _

end GlobalTheory.HodgeCoh
