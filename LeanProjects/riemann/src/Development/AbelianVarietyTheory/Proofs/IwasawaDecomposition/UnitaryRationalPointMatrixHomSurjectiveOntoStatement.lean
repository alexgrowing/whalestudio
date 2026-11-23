import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L), γ₀ ∈ GQ0 L n →
    ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom γ = γ₀ := by
  first | exact @GlobalTheory.AlgWtF.ratHom_surjective | exact GlobalTheory.AlgWtF.ratHom_surjective | (intros; apply GlobalTheory.AlgWtF.ratHom_surjective <;> assumption)
