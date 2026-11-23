import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

noncomputable section

namespace GlobalTheory.ChainDesc

theorem isQuot_cokernel : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h : ℕ) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (H H' : AM B Λ) [H.V.IsQuasicoherent] [H'.V.IsQuasicoherent] (ι : H.V ⟶ freeModule B.X (Fin h)) [Mono ι] (ψ : H' ⟶ H), (∀ (a : Λ) (W : B.X.Opens) (s : Γ(H.V, W)), crd ι W ((H.ρ a : H.V ⟶ H.V).app W s) = mv (RingHom.id _) (M a) (crd ι W s)) → IsQuot M ι (fun W => latOf (ψ.hom ≫ ι) W) (cokernel ψ) (cokernel.π ψ).hom := by
  intro O _ _ _ B Λ _ h M H H' _ _ ι _ ψ hM
  let e : (cokernel ψ).V ≅ cokernel ψ.hom := PreservesCokernel.iso (Action.forget _ _) ψ
  have he : (cokernel.π ψ).hom ≫ e.hom = cokernel.π ψ.hom := PreservesCokernel.π_iso_hom (Action.forget _ _) ψ
  have he' : (cokernel.π ψ).hom = cokernel.π ψ.hom ≫ e.inv := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨isQuasicoherent_of_iso e.symm, fun W hW => ⟨fun y => ?_, fun s => ?_, fun a s s' hs => ?_⟩⟩
  · obtain ⟨s, hs⟩ := surjective_cokernel_π_app ψ.hom hW (e.hom.app W y)
    refine ⟨s, ?_⟩
    rw [he', ← app_app, hs, app_app, e.hom_inv_id]
    rfl
  · have h1 : (cokernel.π ψ).hom.app W s = 0 ↔ (cokernel.π ψ.hom).app W s = 0 := by
      rw [← he, ← app_app]
      exact (map_eq_zero_iff (appLinear e.hom W) (injective_app_of_mono e.hom W)).symm
    rw [h1, exact_cokernel_π_app ψ.hom hW s]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, crd_injective ι W ht⟩
  · obtain rfl : s' = (H.ρ a : H.V ⟶ H.V).app W s := crd_injective ι W (hs.trans (hM a W s).symm)
    rw [app_app, app_app]
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ W s) ((cokernel.π ψ).comm a).symm

end GlobalTheory.ChainDesc

end
