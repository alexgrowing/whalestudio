import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_pow_normV_sub_one' : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ),
    Valued.v ((y : v.adicCompletion E) - 1) < 1 →
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  first | exact @GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | exact GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | (intros; apply GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one <;> assumption)
