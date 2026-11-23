import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProduct
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_period_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l)),
    (∀ μ, μ ∈ s) → (∀ μ, PrePer K χ μ (t μ)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) →
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | exact GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | (intros; apply GlobalTheory.CompanionTheory.LTPer.actB_prod_periods <;> assumption)
