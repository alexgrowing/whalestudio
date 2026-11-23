import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  first | exact @GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | (intros; apply GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts <;> assumption)
