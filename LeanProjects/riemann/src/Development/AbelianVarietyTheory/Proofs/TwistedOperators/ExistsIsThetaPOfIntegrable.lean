import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open MeasureTheory Formalism.IndefR

namespace GlobalTheory.ThetaIntegralLinear

theorem exists_isThetaP_of_integrable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by

  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν)
    ?_ ?_ ?_ ?_, hint, ?_⟩
  · intro f₁ f₂ e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    exact integral_add (hint f₁ e g) (hint f₂ e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e₁ e₂
    funext g
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact integral_add (hint f e₁ g) (hint f e₂ g)
  · intro c f e
    funext g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e g
    rfl

end GlobalTheory.ThetaIntegralLinear
