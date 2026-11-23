import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_properties_residue : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | exact GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | (intros; apply GlobalTheory.CompanionTheory.LTPer.uniformiser_facts <;> assumption)
