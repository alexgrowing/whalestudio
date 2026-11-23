import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem latMap_Lc_iff : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  intro D X n γ hγ
  have key : GlobalTheory.SgGlob.latMap γ (Lc X) =
      (Formalism.HermitianLatticesTheory.gmap n (VS D).L0).comap ((vecOf X).restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [GlobalTheory.SgGlob.latMap, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, Submodule.mem_comap, Lc,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact ⟨vecOf X c', hc', n_vecOf hγ c'⟩
    · rintro ⟨y, hy, hny⟩
      refine ⟨crdH X y, by rw [vecOf_crdH]; exact hy, ?_⟩
      rw [← hγ, hny, crdH_vecOf]
  have hsurj : Function.Surjective ((vecOf X).restrictScalars (𝓞 D.host.E)) := fun y =>
    ⟨crdH X y, vecOf_crdH X y⟩
  rw [key]
  exact (Submodule.comap_injective_of_surjective hsurj).eq_iff

end GlobalTheory.CovDomGrp
