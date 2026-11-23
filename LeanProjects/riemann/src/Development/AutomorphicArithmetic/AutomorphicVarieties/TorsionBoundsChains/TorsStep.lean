import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TorsStep

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.torsStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → TorsLe C c → TorsLe B (a * c) :=
  _root_.UpperTheory.Reformulated.B.Qf15.torsStep
