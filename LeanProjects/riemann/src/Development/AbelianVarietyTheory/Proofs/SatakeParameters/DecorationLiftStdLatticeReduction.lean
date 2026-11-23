import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

theorem decoSet_liftFr_lifts_level :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E)))
      (d : DecoSet E n ST SG) (w : SG),
      (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧
        ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x :=
  fun _ _ _ _ _ _ _ d w => GlobalTheory.TopStep.liftFr_spec d.2 w

end GlobalTheory
