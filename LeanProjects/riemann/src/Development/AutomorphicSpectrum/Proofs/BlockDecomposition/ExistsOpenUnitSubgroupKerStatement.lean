import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKer
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧ (∀ x ∈ U, IsUnitAt w x) ∧
      ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | exact GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | (intros; apply GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker <;> assumption)
