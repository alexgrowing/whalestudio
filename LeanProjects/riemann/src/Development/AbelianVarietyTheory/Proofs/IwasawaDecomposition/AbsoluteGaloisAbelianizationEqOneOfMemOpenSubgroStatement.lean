import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  first | exact @GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | exact GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | (intros; apply GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup <;> assumption)
