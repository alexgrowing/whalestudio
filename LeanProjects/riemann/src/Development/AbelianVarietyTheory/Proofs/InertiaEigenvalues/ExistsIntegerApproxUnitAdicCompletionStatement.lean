import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_approx_unit_adicCompletion : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  first | exact @GlobalTheory.unit_completion_approx_integer | exact GlobalTheory.unit_completion_approx_integer | (intros; apply GlobalTheory.unit_completion_approx_integer <;> assumption)
