import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtendPt
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.extendPt :
    ∀ (O Λ T K : Type) [CommRing O] [CommRing Λ] [CommRing T] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O T] [Algebra Λ T] [IsScalarTower O Λ T] [Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K), P.comap (algebraMap Λ T) ≤ RingHom.ker y → ∃ x : T →ₐ[O] K, P ≤ RingHom.ker x ∧ ∀ a, x (algebraMap Λ T a) = y a :=
  _root_.UpperTheory.Reformulated.B.Qi4.extendPt
