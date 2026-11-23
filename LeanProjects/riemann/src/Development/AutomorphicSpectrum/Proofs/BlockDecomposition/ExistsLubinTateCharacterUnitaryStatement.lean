import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitary
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubin_tate_character_unitary : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | exact GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | (intros; apply GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar <;> assumption)
