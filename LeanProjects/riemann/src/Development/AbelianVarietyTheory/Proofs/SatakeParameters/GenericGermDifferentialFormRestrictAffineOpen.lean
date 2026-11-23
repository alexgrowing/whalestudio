import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh

theorem formGermI_res : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ),
    letI := algΓ p
    ∀ [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p) (j : ℕ) (V V' : Z.Opens)
      (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hη : genericPoint Z ∈ V) (hη' : genericPoint Z ∈ V')
      (h : V' ≤ V) (y : sectionsOn (Omega p j) V),
      formGermI p j hV' hη' hinst (sectionsOn.res ℂ (Omega p j) h y) = formGermI p j hV hη hinst y := by
  intro Z _ p
  letI := algΓ p
  intro inst hinst j V V' hV hV' hη hη' h y
  subst hinst
  letI := ffAlg p
  have key : (toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) =
      formRes p h j ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y)) := by
    apply (toOmEquiv p j hV').injective
    rw [LinearEquiv.apply_symm_apply, toOmEquiv_apply, ← res_toOm, ← toOmEquiv_apply p j hV,
      LinearEquiv.apply_symm_apply, sectionsOn.toΓ_res]
  change (semiHom_germSec p hη').mDR
      ((toOmEquiv p j hV').symm (sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p j) h y)) : DR ℂ (Sec p V')) =
    (semiHom_germSec p hη).mDR ((toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) : DR ℂ (Sec p V))
  rw [key]
  exact congrArg Subtype.val (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res p h)) (semiHom_germSec p hη')
    (semiHom_germSec p hη) (fun b ↦ by
      change (Z.presheaf.germ V' (genericPoint Z) hη').hom ((Z.presheaf.map (homOfLE h).op).hom b) =
        (Z.presheaf.germ V (genericPoint Z) hη).hom b
      exact congrArg (fun f ↦ f.hom (show Γ(Z, V) from b))
        (TopCat.Presheaf.germ_res Z.presheaf (homOfLE h) (genericPoint Z) hη')) _)

end GlobalTheory.HodgeCoh
