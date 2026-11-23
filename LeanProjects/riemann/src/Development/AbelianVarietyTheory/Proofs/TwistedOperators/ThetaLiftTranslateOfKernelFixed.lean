import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.thetaLift_translate_of_kernel_fixed : ∀ {G H S Sinf Ds Dt : Type} [Group G] [Group H]
    [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt),
    _root_.Formalism.IndefR.Lift.IsIo ν 𝓕 th pt It CCs CCt io →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (It φ v) = 0) → u = 0) →
    ∀ (k : G) (k' : H) (a a' : ℂ), (∀ g h φ, a * th (g * k) (h * k') (pt φ) = a' * th g h (pt φ)) →
    (∀ (F : CCs) φ v g, ∫ h in 𝓕, th g (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') ∂ν =
      ∫ h in 𝓕, th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h ∂ν) →
    ∀ (F F' : CCs) (u : CCt), (∀ v h, (F' : Ds →ₗ[ℂ] (H → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) →
    (∀ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) v g = a * ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) v (g * k)) →
    io F' = u := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ _ _ ν 𝓕 th pt It CCs CCt io hio hker k k' a a' hth hinv
    F F' u hF' hu
  refine sub_eq_zero.mp (hker (io F' - u) fun φ v => ?_)
  funext g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [sub_eq_zero, ← hio.eq F' φ v g, hu, ← hio.eq F φ v (g * k)]
  unfold _root_.Formalism.IndefR.Lift.liftInt
  rw [← hinv F φ v (g * k), ← integral_const_mul]
  congr 1
  funext h
  rw [hF', show a * (th (g * k) (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) =
    (a * th (g * k) (h * k') (pt φ)) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') from
    (_root_.mul_assoc _ _ _).symm, hth]
  ring

end GlobalTheory
