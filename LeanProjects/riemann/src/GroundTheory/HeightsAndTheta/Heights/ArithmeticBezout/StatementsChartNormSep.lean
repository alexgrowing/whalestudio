import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SectionLineAnyField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormOfDividedFormSep.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [Infinite O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    (letI := FractionRing.liftAlgebra O (FractionRing B)
     Algebra.IsSeparable (FractionRing O) (FractionRing B)) →
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))

def ChartFracSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (K L : Type) [Field K] [Field L]
    [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
    [Algebra (ChartLoc I t e p) L] [IsFractionRing (ChartLoc I t e p) L] [Algebra K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower (Localization.AtPrime p) (ChartLoc I t e p) L],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I → Algebra.IsSeparable K L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
