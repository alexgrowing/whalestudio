import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProIsometryOfLocalIsometries
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pro_isometry_of_local_isometries : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime | exact GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime <;> assumption)
